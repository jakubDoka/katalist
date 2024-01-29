const std = @import("std");
const Lexer = @import("Lexer.zig");
const EnumList = @import("EnumList.zig");
const Type = @import("Typechk.zig").Type;
const maxIdentLen = @import("Ident.zig").cap;
const garbage = @import("garbage.zig");
const Self = @This();

fn cloneSlice(comptime T: type, allocator: std.mem.Allocator, slice: []const T) ![]T {
    const new = try allocator.alloc(T, slice.len);
    std.mem.copy(T, new, slice);
    return new;
}

pub const Ast = struct {
    pub const Ident = packed struct(u32) {
        last: bool = false,
        len: u6 = 0,
        offset: u25 = 0, // limits to 32 mib, should be enough

        pub fn init(offset: usize, len: usize) Ident {
            std.debug.assert(len <= maxIdentLen);
            return .{ .len = @intCast(len), .offset = @intCast(offset) };
        }

        pub fn slice(self: Ident, src: []const u8) []const u8 {
            return src[self.offset..][0..self.len];
        }

        pub fn eql(self: Ident, other: Ident) bool {
            return self.len == other.len and self.offset == other.offset;
        }
    };

    pub const ItemTag = enum {
        Func,
    };

    pub const Item = union(ItemTag) {
        pub const Store = EnumList.Unmanaged(Item);
        pub const Id = EnumList.Id(ItemTag);

        pub const Func = struct {
            name: Ident,
            params: []Param,
            ret: Expr.Id,
            body: []Expr.Id,
        };

        pub const Param = struct {
            name: Ident,
            type: Expr.Id,
        };

        Func: Func,

        pub fn clone(self: *const Item, alloc: std.mem.Allocator) !Item {
            switch (self.*) {
                .Func => |s| return .{ .Func = .{
                    .name = s.name,
                    .params = try cloneSlice(Param, alloc, s.params),
                    .ret = s.ret,
                    .body = try cloneSlice(Expr.Id, alloc, s.body),
                } },
            }
        }
    };

    pub const ExprTag = enum {
        Ident,
        Int,
        Unary,
        Binary,
        Var,
        Call,
        Item,
        Block,
        Ret,
        BuiltinType,
        Underscore,
    };

    pub const Expr = union(ExprTag) {
        pub const Store = EnumList.Unmanaged(Expr);
        pub const Id = EnumList.Id(ExprTag);

        pub const InfixOp = enum {
            Add,
            Sub,
            Assign,

            pub fn precedense(self: InfixOp) u8 {
                return switch (self) {
                    .Add, .Sub => 8,
                    .Assign => 15,
                };
            }

            pub fn tryFromToken(token: Lexer.Token) ?InfixOp {
                return switch (token) {
                    .Add => .Add,
                    .Sub => .Sub,
                    .Assign => .Assign,
                    else => return null,
                };
            }

            pub fn print(self: InfixOp, writer: anytype) !void {
                return switch (self) {
                    .Add => try writer.writeByte('+'),
                    .Sub => try writer.writeByte('-'),
                    .Assign => try writer.writeAll("="),
                };
            }
        };

        pub const PrefixOp = enum {
            Neg,
        };

        pub const Unary = struct {
            op: PrefixOp,
            expr: Expr.Id,
        };

        pub const Binary = struct {
            op: InfixOp,
            lhs: Expr.Id,
            rhs: Expr.Id,
        };

        pub const Var = struct {
            is_const: bool,
            name: Ident,
            type: ?Expr.Id,
            init: Expr.Id,
        };

        pub const Call = struct {
            callee: Expr.Id,
            args: []Expr.Id,
        };

        pub const Block = []Expr.Id;

        Ident: Ident,
        Int: u64,
        Unary: Unary,
        Binary: Binary,
        Var: Var,
        Call: Call,
        Item: Item.Id,
        Block: Block,
        Ret: Expr.Id,
        BuiltinType: Type.Builtin.Compact,
        Underscore,

        pub fn clone(self: *const Expr, alloc: std.mem.Allocator) !Expr {
            return switch (self.*) {
                .Call => |s| Expr{ .Call = .{
                    .callee = s.callee,
                    .args = try cloneSlice(Expr.Id, alloc, s.args),
                } },
                .Block => |s| Expr{ .Block = try cloneSlice(Expr.Id, alloc, s) },
                else => self.*,
            };
        }
    };

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
    };

    arena: std.heap.ArenaAllocator.State,
    item_store: Item.Store,
    expr_store: Expr.Store,
    items: std.ArrayListUnmanaged(Item.Id),
    errors: std.ArrayListUnmanaged(ErrorMessage),

    pub fn init() Ast {
        return .{
            .arena = .{},
            .item_store = Item.Store.init(),
            .expr_store = Expr.Store.init(),
            .items = .{},
            .errors = .{},
        };
    }

    pub fn deinit(self: *Ast, alloc: std.mem.Allocator) void {
        self.arena.promote(alloc).deinit();
        self.item_store.deinit(alloc);
        self.expr_store.deinit(alloc);
        self.items.deinit(alloc);
        self.errors.deinit(alloc);
    }
};

pub fn Printer(comptime W: type) type {
    return struct {
        const PThis = @This();
        const Item = Ast.Item;
        const Expr = Ast.Expr;
        const WriteError = std.mem.Allocator.Error || W.Error;

        ast: *const Ast,
        writer: W,
        indent: usize,
        source: []const u8,

        pub fn init(ast: *const Ast, writer: W, source: []const u8) PThis {
            return .{ .ast = ast, .writer = writer, .indent = 0, .source = source };
        }

        pub fn print(self: *PThis) WriteError!void {
            for (self.ast.items.items) |item| {
                try self.printItem(item);
                try self.writer.writeByte('\n');
            }
        }

        fn printItem(self: *PThis, item: Item.Id) WriteError!void {
            switch (self.ast.item_store.get(item)) {
                .Func => |s| try self.printFunction(s),
            }
        }

        fn printFunction(self: *PThis, func: Item.Func) WriteError!void {
            try self.writer.writeAll("fn ");
            try self.printIdent(func.name);
            try self.writer.writeByte('(');
            for (func.params, 0..) |param, i| {
                try self.printIdent(param.name);
                try self.writer.writeAll(": ");
                try self.printExpr(param.type);
                if (i + 1 != func.params.len) try self.writer.writeAll(", ");
            }
            try self.writer.writeAll(") ");
            try self.printExpr(func.ret);
            try self.writer.writeByte(' ');
            try self.printBlock(func.body);
        }

        fn printBlock(self: *PThis, block: []Expr.Id) WriteError!void {
            try self.writer.writeAll("{\n");
            self.indent += 1;
            for (block) |expr| {
                try self.printIndent();
                try self.printExpr(expr);
                try self.writer.writeAll(";\n");
            }
            self.indent -= 1;
            try self.printIndent();
            try self.writer.writeByte('}');
        }

        fn printExpr(self: *PThis, expr: Expr.Id) WriteError!void {
            return switch (self.ast.expr_store.get(expr)) {
                .Ident => |s| try self.printIdent(s),
                .Int => |s| try self.writer.print("{d}", .{s}),
                .Binary => |s| try self.printBinary(s),
                .Var => |s| try self.printVar(s),
                .Ret => |s| try self.printRet(s),
                .BuiltinType => |s| try Type.Builtin.expand(s).print(self.writer),
                .Call => |s| try self.printCall(s),
                .Underscore => try self.writer.writeByte('_'),
                else => try self.writer.print("{any}", .{expr}),
            };
        }

        fn printCall(self: *PThis, expr: Expr.Call) WriteError!void {
            try self.printExpr(expr.callee);
            try self.writer.writeByte('(');
            for (expr.args, 0..) |arg, i| {
                try self.printExpr(arg);
                if (i + 1 != expr.args.len) try self.writer.writeAll(", ");
            }
            try self.writer.writeByte(')');
        }

        fn printRet(self: *PThis, expr: Expr.Id) WriteError!void {
            try self.writer.writeAll("ret ");
            try self.printExpr(expr);
        }

        fn printVar(self: *PThis, expr: Expr.Var) WriteError!void {
            try self.writer.writeAll("let ");
            try self.printIdent(expr.name);
            try self.writer.writeAll(" = ");
            try self.printExpr(expr.init);
        }

        fn printBinary(self: *PThis, expr: Expr.Binary) WriteError!void {
            try self.writer.writeByte('(');
            try self.printExpr(expr.lhs);
            try self.writer.writeByte(' ');
            try expr.op.print(self.writer);
            try self.writer.writeByte(' ');
            try self.printExpr(expr.rhs);
            try self.writer.writeByte(')');
        }

        fn printIdent(self: *PThis, ident: Ast.Ident) WriteError!void {
            try self.writer.print("{s}#{d}", .{ ident.slice(self.source), ident.offset });
        }

        fn printIndent(self: *PThis) WriteError!void {
            for (0..self.indent * 4) |_| try self.writer.writeByte(' ');
        }
    };
}

const Error = error{ParsingFailed} || std.mem.Allocator.Error;

const Scope = struct {
    pub const Frame = usize;

    pub const Sym = struct {
        ident: Ast.Ident,
        resolved: bool,
        last_occurence: Occurence,
    };

    pub const Occurence = union(enum) {
        Expr: Ast.Expr.Id,
        Item,
        Param,
        Var,
    };

    symbols: std.ArrayList(Sym),

    pub fn init(allocator: std.mem.Allocator) Scope {
        return .{ .symbols = std.ArrayList(Sym).init(allocator) };
    }

    pub fn deinit(self: *Scope) void {
        self.symbols.deinit();
    }

    pub fn pushFrame(self: *Scope) Frame {
        return self.symbols.items.len;
    }

    pub fn popFrame(self: *Scope, frame: Frame) void {
        var to_keep = frame;
        for (frame..self.symbols.items.len) |i| {
            const sym = self.symbols.items[i];
            if (!sym.resolved) {
                self.symbols.items[to_keep] = sym;
                to_keep += 1;
            }
        }

        self.symbols.items.len = to_keep;
    }

    pub fn add(self: *Scope, loc: Occurence, ident: []const u8, source: []const u8) !Ast.Ident {
        return self.handleSym(loc, ident, source, true);
    }

    pub fn dispatch(self: *Scope, loc: Occurence, ident: []const u8, source: []const u8) !Ast.Ident {
        return self.handleSym(loc, ident, source, false);
    }

    fn handleSym(self: *Scope, loc: Occurence, ident: []const u8, source: []const u8, or_declare: bool) !Ast.Ident {
        var i = self.symbols.items.len;
        while (i > 0) {
            i -= 1;
            const sym = &self.symbols.items[i];
            if (sym.ident.len != ident.len) continue;
            if (sym.resolved and or_declare) continue;
            if (std.mem.eql(u8, sym.ident.slice(source), ident)) {
                sym.resolved = sym.resolved or or_declare;
                sym.last_occurence = loc;
                return sym.ident;
            }
        }

        const pos = @intFromPtr(ident.ptr) - @intFromPtr(source.ptr);
        const sym = Ast.Ident.init(pos, ident.len);
        try self.symbols.append(.{ .ident = sym, .resolved = or_declare, .last_occurence = loc });

        return sym;
    }
};

alloc: std.mem.Allocator,
scratch: *std.heap.ArenaAllocator,
ast: *Ast,
lexer: Lexer,
next_token: Lexer.TokenMeta,
scope: *Scope,

pub fn parse(allocator: std.mem.Allocator, src: []const u8) Error!Ast {
    var ast = Ast.init();
    var lexer = Lexer.init(src);
    const next_token = lexer.nextToken();
    var scratch = std.heap.ArenaAllocator.init(allocator);
    defer scratch.deinit();
    var scope = Scope.init(allocator);
    defer scope.deinit();

    var self = Self{
        .alloc = allocator,
        .scratch = &scratch,
        .ast = &ast,
        .lexer = lexer,
        .next_token = next_token,
        .scope = &scope,
    };

    self.parseItems() catch |err| {
        if (err == Error.ParsingFailed) return ast;
        ast.deinit(allocator);
        return err;
    };

    try self.popFrame(0); // filter out dispatched symbols, leavin undefined symbols

    for (scope.symbols.items) |sym| {
        try self.addError(.{ .UndeclaredIdent = .{
            .ident = sym.ident.slice(self.lexer.source),
            .pos = sym.ident.offset,
        } });
    }

    return ast;
}

pub fn parseItems(self: *Self) Error!void {
    while (self.next_token.kind != .Eof) {
        if (!self.scratch.reset(.retain_capacity)) return Error.OutOfMemory;
        const item = try self.parseItem();
        try self.addFileItem(item);
    }
}

pub fn parseItem(self: *Self) Error!Ast.Item {
    var token = self.advance();
    return switch (token.kind) {
        .KeyFn => .{ .Func = try self.parseFunction() },
        else => return self.failExpect(token, &.{.KeyFn}),
    };
}

pub fn parseFunction(self: *Self) Error!Ast.Item.Func {
    var ident = try self.expectAdvance(.Ident);
    const name = try self.scope.add(.Item, ident.source, self.lexer.source);

    const frame = self.scope.pushFrame();

    _ = try self.expectAdvance(.LParen);
    const params = try self.parseList(Ast.Item.Param, .RParen, .Comma, parseParam);
    const ret = try self.parseExpr();
    const body = try self.parseBlock();

    try self.popFrame(frame);

    return .{
        .name = name,
        .params = params,
        .ret = ret,
        .body = body,
    };
}

fn popFrame(self: *Self, frame: Scope.Frame) !void {
    for (self.scope.symbols.items[frame..]) |sym| {
        switch (sym.last_occurence) {
            .Expr => |e| switch (self.ast.expr_store.get_ptr(e)) {
                .Ident => |i| i.last = true,
                else => unreachable,
            },
            .Param, .Var => {
                try self.ast.errors.append(self.alloc, .{ .UnusedSymbol = .{
                    .ident = sym.ident.slice(self.lexer.source),
                    .pos = sym.ident.offset,
                } });
            },
            else => {},
        }
    }

    self.scope.popFrame(frame);
}

fn parseBlock(self: *Self) Error!Ast.Expr.Block {
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

fn parseParam(self: *Self) Error!Ast.Item.Param {
    var ident = try self.expectAdvance(.Ident);
    const name = try self.scope.add(.Param, ident.source, self.lexer.source);

    _ = try self.expectAdvance(.Colon);
    const ty = try self.parseExpr();

    return .{
        .name = name,
        .type = ty,
    };
}

fn parseExpr(self: *Self) Error!Ast.Expr.Id {
    return try self.parseExprPrec(255, try self.parseUnitExpr());
}

fn parseExprPrec(self: *Self, prec: u8, initial: Ast.Expr.Id) Error!Ast.Expr.Id {
    var left = initial;
    while (true) {
        const next_op = Ast.Expr.InfixOp.tryFromToken(self.next_token.kind) orelse return left;
        const next_prec = next_op.precedense();

        if (next_prec > prec) return left;
        _ = self.advance();

        left = try self.addExpr(.{ .Binary = .{
            .op = next_op,
            .lhs = left,
            .rhs = try self.parseExprPrec(next_prec, try self.parseUnitExpr()),
        } });
    }
}

fn parseUnitExpr(self: *Self) Error!Ast.Expr.Id {
    const compact = Type.Builtin.compact;
    var token = self.advance();
    var unit: Ast.Expr = switch (token.kind) {
        .Ident => .{ .Ident = try self.scope.dispatch(
            .{ .Expr = self.ast.expr_store.nextId(.Ident) },
            token.source,
            self.lexer.source,
        ) },
        .Underscore => .{ .Underscore = {} },
        .KeyVoid => .{ .BuiltinType = compact(.Void) },
        .KeyUsize => .{ .BuiltinType = compact(.{ .Int = Type.Int.Usize }) },
        .KeyIsize => .{ .BuiltinType = compact(.{ .Int = Type.Int.Isize }) },
        .Int, .Uint => .{ .BuiltinType = compact(.{ .Int = .{
            .signed = token.kind == .Int,
            .bit_width = std.fmt.parseInt(u15, token.source[1..], 10) catch unreachable,
        } }) },
        .Number => .{ .Int = std.fmt.parseInt(u64, token.source, 10) catch |err| b: {
            try self.addError(.{ .InvalidNumber = .{
                .err = err,
                .pos = token.pos,
            } });
            break :b 0;
        } },
        .Sub => .{ .Unary = .{
            .op = .Neg,
            .expr = try self.parseUnitExpr(),
        } },
        .KeyReturn => .{ .Ret = try self.parseExpr() },
        .KeyVar, .KeyConst => .{ .Var = try self.parseVar(token.kind == .KeyConst) },
        else => return self.failExpect(token, &.{ .Ident, .Number, .Sub, .KeyReturn }),
    };

    while (true) {
        switch (self.next_token.kind) {
            .LParen => unit = try self.parseCallExpr(unit),
            else => return try self.addExpr(unit),
        }
    }
}

fn parseVar(self: *Self, is_const: bool) Error!Ast.Expr.Var {
    var ident = try self.expectAdvance(.Ident);

    var ty = if (self.tryAdvance(.Colon) != null) try self.parseUnitExpr() else null;

    _ = try self.expectAdvance(.Assign);
    const init = try self.parseExpr();

    const name = try self.scope.add(.Var, ident.source, self.lexer.source);

    return .{
        .is_const = is_const,
        .name = name,
        .type = ty,
        .init = init,
    };
}

fn parseCallExpr(self: *Self, callee: Ast.Expr) Error!Ast.Expr {
    _ = self.advance();
    const args = try self.parseList(Ast.Expr.Id, .RParen, .Comma, parseExpr);
    return .{ .Call = .{
        .callee = try self.addExpr(callee),
        .args = args,
    } };
}

fn parseList(
    self: *Self,
    comptime T: type,
    comptime end: Lexer.Token,
    comptime sep: Lexer.Token,
    parser: fn (*Self) Error!T,
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

fn expectAdvance(self: *Self, comptime expected: Lexer.Token) Error!Lexer.TokenMeta {
    if (self.next_token.kind == expected) {
        return self.advance();
    } else {
        return self.failExpect(self.next_token, &.{expected});
    }
}

fn tryAdvance(self: *Self, comptime expected: Lexer.Token) ?Lexer.TokenMeta {
    if (self.next_token.kind == expected) {
        return self.advance();
    } else {
        return null;
    }
}

fn advance(self: *Self) Lexer.TokenMeta {
    defer self.next_token = self.lexer.nextToken();
    return self.next_token;
}

fn failExpect(self: *Self, got: Lexer.TokenMeta, comptime expected: []const Lexer.Token) Error {
    try self.addError(.{ .UnexpectedToken = .{
        .expected = expected,
        .actual = got.kind,
        .pos = got.pos,
    } });

    return Error.ParsingFailed;
}

fn scratchBuf(self: *Self, comptime T: type) std.ArrayList(T) {
    return std.ArrayList(T).init(self.scratch.allocator());
}

pub fn addItem(self: *Self, item: Ast.Item) !Ast.Item.Id {
    var arena = self.ast.arena.promote(self.alloc);
    defer self.ast.arena = arena.state;
    return try self.ast.item_store.push(self.alloc, try item.clone(arena.allocator()));
}

pub fn addExpr(self: *Self, expr: Ast.Expr) !Ast.Expr.Id {
    var arena = self.ast.arena.promote(self.alloc);
    defer self.ast.arena = arena.state;
    return try self.ast.expr_store.push(self.alloc, try expr.clone(arena.allocator()));
}

pub fn addError(self: *Self, err: Ast.ErrorMessage) !void {
    try self.ast.errors.append(self.alloc, err);
}

pub fn addFileItem(self: *Self, item: Ast.Item) !void {
    try self.ast.items.append(self.alloc, try self.addItem(item));
}

test {
    std.testing.refAllDeclsRecursive(Self);

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
    ;

    var alloc = garbage.CountingAllocator.init(std.testing.allocator);

    var now = try std.time.Instant.now();
    var ast = try Self.parse(alloc.allocator(), src);
    var elapsed = (try std.time.Instant.now()).since(now);
    std.log.info("elapsed: {d}ns, expansion ratio: {any}", .{ elapsed, @as(f32, @floatFromInt(alloc.count_total)) / @as(f32, @floatFromInt(src.len)) });
    alloc.print();

    defer ast.deinit(alloc.allocator());

    for (ast.errors.items) |err| {
        switch (err) {
            inline else => |v, t| std.log.err("unexpected error: {any} {any}", .{ v, t }),
        }
    }

    var arr = [1]u8{0} ** 10000;
    var buf = std.io.fixedBufferStream(&arr);
    var writer = buf.writer();
    var printer = Printer(@TypeOf(writer)).init(&ast, writer, src);
    try printer.print();

    std.log.info("{s}", .{arr});
}
