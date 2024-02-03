const std = @import("std");
const Lexer = @import("Lexer.zig");
const EnumList = @import("EnumList.zig");
const Ast = @import("Parser/Ast.zig");
const Scope = @import("Parser/Scope.zig");
const maxIdentLen = @import("Ident.zig").cap;
const garbage = @import("garbage.zig");
const Parser = @This();

const Error = error{ParsingFailed} || std.mem.Allocator.Error;

pub const ErrorMessage = union(enum) {
    UnexpectedToken: struct {
        expected: []const Lexer.Token,
        actual: Lexer.Token,
        pos: usize,
    },
    UndeclaredIdent: struct {
        ident: []const u8,
        pos: usize,
    },
    UnusedSymbol: struct {
        ident: []const u8,
        pos: usize,
    },
    InvalidNumber: struct {
        err: std.fmt.ParseIntError,
        pos: usize,
    },
    DuplicateIdent: struct {
        ident: []const u8,
        pos: usize,
    },

    pub fn print(self: ErrorMessage, writer: anytype, src: []const u8) !void {
        const pos = switch (self) {
            inline else => |v| v.pos,
        };
        var line_start = std.mem.lastIndexOfScalar(u8, src[0..pos], '\n') orelse 0;
        line_start += @intFromBool(line_start != 0);

        var line_end = std.mem.indexOfScalar(u8, src[pos..], '\n') orelse src.len - pos;
        line_end += pos;

        var split = std.mem.splitScalar(u8, src[0..line_end], '\n');
        var line: usize = 0;
        while (split.next() != null) line += 1;

        const column = pos - line_start;

        const err = switch (self) {
            .UnexpectedToken => "unexpected token",
            .UndeclaredIdent => "undeclared identifier",
            .UnusedSymbol => "unused symbol",
            .InvalidNumber => "invalid number",
            .DuplicateIdent => "duplicate identifier",
        };

        const padding = [_]u8{' '} ** 200;
        try writer.print(
            "error: {s} at {d}:{d}:{d}\n{s}\n{s}^\n",
            .{ err, line, column, pos, src[line_start..line_end], padding[0..@min(column, 200)] },
        );
    }
};

scratch: *std.heap.ArenaAllocator,
errors: *std.ArrayListUnmanaged(ErrorMessage),
ast: *Ast,
scope: *Scope,
temp_exprs: *Ast.Expr.Store,
temp_items: *Ast.Item.Store,
alloc: std.mem.Allocator,
expr_cp: Ast.Expr.Store.Checkpoint,
item_cp: Ast.Item.Store.Checkpoint,
lexer: Lexer,
next_token: Lexer.TokenMeta,

pub fn parse(
    allocator: std.mem.Allocator,
    src: []const u8,
    errors: *std.ArrayListUnmanaged(ErrorMessage),
) Error!Ast {
    var ast = Ast.init();
    var lexer = Lexer.init(src);
    const next_token = lexer.nextToken();
    var scratch = std.heap.ArenaAllocator.init(allocator);
    defer scratch.deinit();
    var scope = Scope.init(allocator);
    defer scope.deinit();

    var exprs = Ast.Expr.Store.init();
    defer exprs.deinit(allocator);
    var items = Ast.Item.Store.init();
    defer items.deinit(allocator);

    var self = Parser{
        .scratch = &scratch,
        .errors = errors,
        .ast = &ast,
        .scope = &scope,
        .alloc = allocator,
        .temp_exprs = &exprs,
        .temp_items = &items,
        .expr_cp = exprs.checkpoint(),
        .item_cp = items.checkpoint(),
        .lexer = lexer,
        .next_token = next_token,
    };

    const record = self.parseRecordItems() catch |err| {
        if (err == Error.ParsingFailed) return ast;
        ast.deinit(allocator);
        return err;
    };

    try self.popFrame(.{});
    ast.peak_sym_count = scope.peak_ordered_sym_count;
    ast.root = record;

    for (scope.symbols.items) |sym| {
        try self.addError(.{ .UndeclaredIdent = .{
            .ident = sym.ident.slice(self.lexer.source),
            .pos = sym.ident.offset,
        } });
    }

    return ast;
}

fn parseItems(self: *Parser) Error!void {
    const terminals = [_]Lexer.Token{ .Eof, .RBrace, .Unknown };
    while (std.mem.indexOfScalar(Lexer.Token, &terminals, self.next_token.kind) == null) {
        if (!self.scratch.reset(.retain_capacity)) return Error.OutOfMemory;
        const item = try self.parseItem();
        try self.addItem(item);
    }
}

fn parseItem(self: *Parser) Error!Ast.Item {
    var token = self.advance();
    return switch (token.kind) {
        .KeyFn => .{ .Func = try self.parseFunction() },
        .Ident => .{ .Field = try self.parseField(token) },
        else => return self.failExpect(token, &.{.KeyFn}),
    };
}

fn parseField(self: *Parser, ident: Lexer.TokenMeta) Error!Ast.Item.Field {
    const cp = self.temp_exprs.checkpoint();

    _ = try self.expectAdvance(.Colon);
    const ty = try self.parseExpr();
    if (self.tryAdvance(.Comma) == null and
        self.next_token.kind != .RBrace and
        self.next_token.kind != .Semi)
    {
        try self.addError(.{ .UnexpectedToken = .{
            .expected = &.{ .Comma, .RBrace, .Semi },
            .actual = self.next_token.kind,
            .pos = self.next_token.pos,
        } });
        return Error.ParsingFailed;
    }

    return .{
        .slice = try self.temp_exprs.drainInto(&self.ast.exprs, cp, self.alloc),
        .name = Ast.Ident.init(ident.pos, ident.source.len, 0, true),
        .type = ty,
    };
}

fn parseFunction(self: *Parser) Error!Ast.Item.Func {
    var ident = try self.expectAdvance(.Ident);
    const name = try self.addSymbol(.Item, ident.source);

    const frame = self.scope.pushFrame();
    const cp = self.temp_exprs.checkpoint();

    _ = try self.expectAdvance(.LParen);
    const params = try self.parseList(Ast.Item.Param, .RParen, .Comma, parseParam);
    const ret = try self.parseExpr();
    const body = try self.parseBlock();

    try self.popFrame(frame);

    return .{
        .slice = try self.temp_exprs.drainInto(&self.ast.exprs, cp, self.alloc),
        .name = name,
        .params = params,
        .ret = ret,
        .body = body,
    };
}

fn addSymbol(self: *Parser, kind: Scope.Occurence, ident: []const u8) !Ast.Ident {
    return self.scope.add(kind, ident, self.lexer.source) catch |err| switch (err) {
        error.DuplicateSymbol => {
            try self.addError(.{ .DuplicateIdent = .{
                .ident = ident,
                .pos = @intFromPtr(ident.ptr) - @intFromPtr(self.lexer.source.ptr),
            } });
            return error.ParsingFailed;
        },
        else => |e| return e,
    };
}

fn popFrame(self: *Parser, frame: Scope.Frame) !void {
    for (self.scope.symbols.items[frame.sym_count..]) |sym| {
        if (!sym.resolved) continue;
        switch (sym.last_occurence) {
            .Expr => |e| {
                switch (self.temp_exprs.get(self.expr_cp, e)) {
                    .Ident => |i| i.last = true,
                    else => unreachable,
                }
            },
            .Param, .Var => if (!sym.used) {
                try self.errors.append(self.alloc, .{ .UnusedSymbol = .{
                    .ident = sym.ident.slice(self.lexer.source),
                    .pos = sym.ident.offset,
                } });
            },
            else => {},
        }
    }

    self.scope.popFrame(frame);
}

fn parseBlock(self: *Parser) Error!Ast.Expr.Block {
    var buf = self.scratchBuf(Ast.Expr.Id);

    _ = try self.expectAdvance(.LBrace);

    const frame = self.scope.pushFrame();
    while (self.next_token.kind != .RBrace) {
        const stmt = try self.parseExpr();
        try buf.append(stmt);
        _ = try self.expectAdvance(.Semi);
    }
    _ = self.advance();
    try self.popFrame(frame);

    return buf.items;
}

fn parseParam(self: *Parser) Error!Ast.Item.Param {
    var ident = try self.expectAdvance(.Ident);
    const name = try self.addSymbol(.Param, ident.source);

    _ = try self.expectAdvance(.Colon);
    const ty = try self.parseExpr();

    return .{
        .name = name,
        .type = ty,
    };
}

fn parseExpr(self: *Parser) Error!Ast.Expr.Id {
    return try self.parseExprPrec(255, try self.parseUnitExpr());
}

fn parseExprPrec(self: *Parser, prec: u8, initial: Ast.Expr.Id) Error!Ast.Expr.Id {
    var left = initial;
    while (true) {
        const next_op = Ast.Expr.InfixOp.tryFromToken(self.next_token.kind) orelse return left;
        const next_prec = next_op.precedense();

        if (next_prec >= prec) return left;
        _ = self.advance();

        left = try self.addExpr(.{ .Binary = .{
            .op = next_op,
            .lhs = left,
            .rhs = try self.parseExprPrec(next_prec, try self.parseUnitExpr()),
        } });
    }
}

fn parseUnitExpr(self: *Parser) Error!Ast.Expr.Id {
    const compact = Ast.Builtin.compact;
    var token = self.advance();
    var unit: Ast.Expr = switch (token.kind) {
        .Ident => .{ .Ident = try self.dispatchSymbol(
            .{ .Expr = self.temp_exprs.nextId(.Ident) },
            token.source,
        ) },
        .LParen => b: {
            const expr = try self.parseExpr();
            _ = try self.expectAdvance(.RParen);
            break :b .{ .Parens = expr };
        },
        .Underscore => .{ .Underscore = {} },
        .KeyVoid => .{ .BuiltinType = compact(.Void) },
        .KeyType => .{ .BuiltinType = compact(.Type) },
        .KeyUsize => .{ .BuiltinType = compact(.{ .Int = Ast.Int.Usize }) },
        .KeyIsize => .{ .BuiltinType = compact(.{ .Int = Ast.Int.Isize }) },
        .Int, .Uint => .{ .BuiltinType = compact(.{ .Int = .{
            .signed = token.kind == .Int,
            .bit_width = std.fmt.parseInt(u15, token.source[1..], 10) catch unreachable,
        } }) },
        .KeyBool => .{ .BuiltinType = compact(.Bool) },
        .KeyFalse, .KeyTrue => .{ .Bool = token.kind == .KeyTrue },
        .Number => .{ .Int = std.fmt.parseInt(u64, token.source, 10) catch |err| {
            try self.addError(.{ .InvalidNumber = .{
                .err = err,
                .pos = token.pos,
            } });
            return Error.ParsingFailed;
        } },
        .Sub => .{ .Unary = .{
            .op = .Neg,
            .expr = try self.parseUnitExpr(),
        } },
        .KeyReturn => .{ .Ret = try self.parseExpr() },
        .KeyVar, .KeyConst => .{ .Var = try self.parseVar(token.kind == .KeyConst) },
        .KeyIf => .{ .If = try self.parseIf() },
        .KeyStruct => .{ .Record = try self.parseRecord() },
        else => return self.failExpect(token, &.{}),
    };

    while (true) {
        switch (self.next_token.kind) {
            .LParen => unit = try self.parseCallExpr(unit),
            else => return try self.addExpr(unit),
        }
    }
}

fn parseRecord(self: *Parser) Error!Ast.Expr.Id.Index {
    _ = try self.expectAdvance(.LBrace);
    const record = try self.parseRecordItems();
    _ = try self.expectAdvance(.RBrace);

    const id = self.ast.children.items.len;
    try self.ast.children.append(self.alloc, record);
    return @intCast(id);
}

fn parseRecordItems(self: *Parser) Error!Ast.Record {
    var saved_cp = self.item_cp;
    defer self.item_cp = saved_cp;
    self.item_cp = self.temp_items.checkpoint();

    try self.parseItems();
    const slice = try self.temp_items.drainInto(&self.ast.items, self.item_cp, self.alloc);
    return .{ .items = slice, .kind = .Struct };
}

fn dispatchSymbol(self: *Parser, kind: Scope.Occurence, ident: []const u8) !Ast.Ident {
    return self.scope.dispatch(
        kind,
        ident,
        self.lexer.source,
    ) catch |err| switch (err) {
        error.DuplicateSymbol => unreachable,
        else => |e| return e,
    };
}

fn parseIf(self: *Parser) Error!Ast.Expr.If {
    _ = try self.expectAdvance(.LParen);
    const cond = try self.parseExpr();
    _ = try self.expectAdvance(.RParen);
    const then = try self.parseExpr();
    const els = if (self.tryAdvance(.KeyElse) != null) try self.parseExpr() else null;

    return .{
        .cond = cond,
        .then = then,
        .els = els,
    };
}

fn parseVar(self: *Parser, is_const: bool) Error!Ast.Expr.Var {
    var ident = try self.expectAdvance(.Ident);

    var ty = if (self.tryAdvance(.Colon) != null) try self.parseUnitExpr() else null;

    _ = try self.expectAdvance(.Assign);
    const init = try self.parseExpr();

    const name = try self.addSymbol(.Var, ident.source);

    return .{
        .is_const = is_const,
        .name = name,
        .type = ty,
        .init = init,
    };
}

fn parseCallExpr(self: *Parser, callee: Ast.Expr) Error!Ast.Expr {
    _ = self.advance();
    return .{ .Call = .{
        .callee = try self.addExpr(callee),
        .args = try self.parseList(Ast.Expr.Id, .RParen, .Comma, parseExpr),
    } };
}

fn parseList(
    self: *Parser,
    comptime T: type,
    comptime end: Lexer.Token,
    comptime sep: Lexer.Token,
    parser: fn (*Parser) Error!T,
) Error![]T {
    var list = self.scratchBuf(T);

    while (self.next_token.kind != end) {
        const elem = try parser(self);
        try list.append(elem);
        if (self.next_token.kind == end) break;
        _ = try self.expectAdvance(sep);
    }
    _ = self.advance();

    return list.items;
}

fn expectAdvance(self: *Parser, comptime expected: Lexer.Token) Error!Lexer.TokenMeta {
    if (self.next_token.kind == expected) {
        return self.advance();
    } else {
        return self.failExpect(self.next_token, &.{expected});
    }
}

fn tryAdvance(self: *Parser, comptime expected: Lexer.Token) ?Lexer.TokenMeta {
    if (self.next_token.kind == expected) {
        return self.advance();
    } else {
        return null;
    }
}

fn advance(self: *Parser) Lexer.TokenMeta {
    defer self.next_token = self.lexer.nextToken();
    return self.next_token;
}

fn failExpect(self: *Parser, got: Lexer.TokenMeta, comptime expected: []const Lexer.Token) Error {
    try self.addError(.{ .UnexpectedToken = .{
        .expected = expected,
        .actual = got.kind,
        .pos = got.pos,
    } });

    return Error.ParsingFailed;
}

fn scratchBuf(self: *Parser, comptime T: type) std.ArrayList(T) {
    return std.ArrayList(T).init(self.scratch.allocator());
}

fn addItem(self: *Parser, item: Ast.Item) !void {
    const name = item.name();
    var arena = self.ast.arena.promote(self.alloc);
    const allocated = try item.clone(arena.allocator());
    self.ast.arena = arena.state;
    const id = try self.temp_items.pushAbsolute(self.alloc, allocated);
    if (name.index >= self.ast.item_lookup.items.len)
        try self.ast.item_lookup.resize(self.alloc, name.index + 1);
    self.ast.item_lookup.items[name.index] = id;
}

fn addExpr(self: *Parser, expr: Ast.Expr) !Ast.Expr.Id {
    var arena = self.ast.arena.promote(self.alloc);
    defer self.ast.arena = arena.state;
    return try self.temp_exprs.push(self.alloc, self.expr_cp, try expr.clone(arena.allocator()));
}

fn addError(self: *Parser, err: ErrorMessage) !void {
    try self.errors.append(self.alloc, err);
}

test {
    const src =
        \\fn main() usize { return 1 + 2; }
        \\fn assign(a: u8, b: u8) void { a = b + 2; }
        \\fn bull(a: i3, b: i3) void { a + b = 2; }
        \\fn call_main() usize { return main(2) + 1; }
        \\fn variables() u64 { const a = 1; const b = 2; return a + b; }
        \\fn more_math() usize {
        \\    const foo = 0;
        \\    const goo = 2;
        \\    const soo = 5;
        \\    const sub = foo + goo + soo;
        \\    return foo - goo = sub;
        \\}
        \\fn createSturct() type { return struct { a: u8, b: u8 }; }
    ;

    var alloc = garbage.CountingAllocator.init(std.testing.allocator);
    var errors = std.ArrayListUnmanaged(ErrorMessage){};
    defer errors.deinit(alloc.allocator());

    var now = try std.time.Instant.now();
    var ast = try parse(alloc.allocator(), src, &errors);
    defer ast.deinit(alloc.allocator());
    var elapsed = (try std.time.Instant.now()).since(now);
    std.log.info("elapsed: {d}ns, expansion ratio: {any}", .{
        elapsed,
        @as(f32, @floatFromInt(alloc.count_total)) / @as(f32, @floatFromInt(src.len)),
    });
    alloc.print();
    for (errors.items) |err| {
        std.log.err("unexpected error:", .{});
        try err.print(std.io.getStdErr().writer(), src);
    }
    try std.testing.expectEqual(errors.items.len, 0);

    var arr = [1]u8{0} ** 10000;
    var buf = std.io.fixedBufferStream(&arr);
    var writer = buf.writer();
    var printer = Ast.Printer(@TypeOf(writer)).init(&ast, writer, src);
    try printer.print();

    std.log.info("{s}", .{arr});
}
