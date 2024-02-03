const std = @import("std");
const EnumList = @import("../EnumList.zig");
const Lexer = @import("../Lexer.zig");
const Ast = @This();

fn cloneSlice(comptime T: type, allocator: std.mem.Allocator, slice: []const T) ![]T {
    const new = try allocator.alloc(T, slice.len);
    std.mem.copy(T, new, slice);
    return new;
}

pub const Int = packed struct(u16) {
    pub const maxWidth: u15 = ~@as(u15, 0) - std.meta.fields(Builtin).len + 1;
    pub const Usize = Int{ .bit_width = 64 };
    pub const Isize = Int{ .signed = true, .bit_width = 64 };
    pub const Ctint = Int{ .signed = true, .bit_width = maxWidth };

    signed: bool = false,
    bit_width: u15,

    pub fn parse(str: []const u8) ?Int {
        if (str.len < 2) return null;

        const sign = switch (str[0]) {
            'u' => true,
            'i' => false,
            else => return null,
        };

        const bit_width = std.fmt.parseInt(u15, str[1..], 10) catch return null;
        if (bit_width == 0) return null;

        return .{ .signed = sign, .bit_width = bit_width };
    }

    pub fn print(self: Int, writer: anytype) !void {
        try std.fmt.format(writer, "{s}{d}", .{ if (self.signed) "i" else "u", self.bit_width });
    }

    pub fn isCt(self: Int) bool {
        return self.bit_width == Ctint.bit_width;
    }
};

pub const Builtin = union(enum) {
    pub const Compact = u16;

    Void,
    Type,
    Decl,
    Bool,
    Int: Int,

    pub fn print(self: Builtin, writer: anytype) !void {
        switch (self) {
            .Int => |i| try i.print(writer),
            inline else => |_, tag| {
                const name = @tagName(tag);
                comptime var low_name: [name.len]u8 = undefined;
                inline for (&low_name, name) |*d, s| d.* = comptime std.ascii.toLower(s);
                try writer.writeAll(&low_name);
            },
        }
    }

    pub fn compact(self: Builtin) Compact {
        return switch (self) {
            .Int => |i| @bitCast(i),
            inline else => |_, tag| Int.maxWidth + @as(Compact, @intFromEnum(tag)),
        };
    }

    pub fn expand(self: Compact) Builtin {
        if (self < Int.maxWidth) return .{ .Int = @bitCast(self) };
        const Tag = std.meta.Tag(Builtin);
        return switch (@as(Tag, @enumFromInt(@as(Compact, self - Int.maxWidth)))) {
            .Int => .{ .Int = @bitCast(self) },
            inline else => |tag| @unionInit(Builtin, @tagName(tag), {}),
        };
    }
};

pub const Ident = packed struct(u64) {
    last: bool = false,
    len: u6,
    offset: u24,
    unordered: bool,
    index: u32,

    pub fn init(offset: usize, len: usize, index: usize, unordered: bool) Ident {
        return .{
            .len = @intCast(len),
            .offset = @intCast(offset),
            .index = @intCast(index),
            .unordered = unordered,
        };
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
    Field,
};

pub const Item = union(ItemTag) {
    pub const Store = EnumList.Unmanaged(Item);
    pub const Id = EnumList.Id(ItemTag);

    pub const Field = struct {
        slice: Expr.Store.Slice,
        name: Ident,
        type: Expr.Id,
    };

    pub const Func = struct {
        slice: Expr.Store.Slice,
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
    Field: Field,

    pub fn clone(self: *const Item, alloc: std.mem.Allocator) !Item {
        switch (self.*) {
            .Func => |s| return .{ .Func = .{
                .slice = s.slice,
                .name = s.name,
                .params = try cloneSlice(Param, alloc, s.params),
                .ret = s.ret,
                .body = try cloneSlice(Expr.Id, alloc, s.body),
            } },
            else => return self.*,
        }
    }

    pub fn name(self: *const Item) Ident {
        return switch (self.*) {
            .Func => |s| s.name,
            .Field => |s| s.name,
        };
    }
};

pub const ExprTag = enum {
    Ident,
    Int,
    Bool,
    Unary,
    Binary,
    Var,
    Call,
    Item,
    Block,
    Ret,
    If,
    BuiltinType,
    Underscore,
    Parens,
    Record,
};

pub const Expr = union(ExprTag) {
    pub const Store = EnumList.Unmanaged(Expr);
    pub const Id = EnumList.Id(ExprTag);

    pub const InfixOp = enum {
        Add,
        Sub,
        Assign,
        Eq,
        Ne,
        Lt,
        Gt,
        Le,
        Ge,

        pub fn precedense(self: InfixOp) u8 {
            return switch (self) {
                .Add, .Sub => 8,
                .Eq, .Ne, .Lt, .Gt, .Le, .Ge => 9,
                .Assign => 15,
            };
        }

        pub fn isCommutative(self: InfixOp) bool {
            return switch (self) {
                .Add, .Eq, .Ne => true,
                else => false,
            };
        }

        pub fn mutatesOperand(self: InfixOp) bool {
            return switch (self) {
                .Add, .Sub => true,
                else => false,
            };
        }

        pub fn tryFromToken(token: Lexer.Token) ?InfixOp {
            return switch (token) {
                inline else => |t| {
                    if (!@hasField(InfixOp, @tagName(t))) return null;
                    return @field(InfixOp, @tagName(t));
                },
            };
        }

        pub fn print(self: InfixOp, writer: anytype) !void {
            return switch (self) {
                .Add => try writer.writeByte('+'),
                .Sub => try writer.writeByte('-'),
                .Assign => try writer.writeAll("="),
                .Eq => try writer.writeAll("=="),
                .Ne => try writer.writeAll("!="),
                .Lt => try writer.writeAll("<"),
                .Gt => try writer.writeAll(">"),
                .Le => try writer.writeAll("<="),
                .Ge => try writer.writeAll(">="),
            };
        }
    };

    pub const PrefixOp = enum {
        Neg,
    };

    pub const Unary = struct {
        op: PrefixOp,
        expr: Id,
    };

    pub const Binary = struct {
        op: InfixOp,
        lhs: Id,
        rhs: Id,
    };

    pub const Var = struct {
        is_const: bool,
        name: Ident,
        type: ?Id,
        init: Id,
    };

    pub const Call = struct {
        callee: Id,
        args: []Id,
    };

    pub const If = struct {
        cond: Id,
        then: Id,
        els: ?Id,
    };

    pub const Block = []Expr.Id;

    Ident: Ident,
    Int: u64,
    Bool: bool,
    Unary: Unary,
    Binary: Binary,
    Var: Var,
    Call: Call,
    Item: Item.Id,
    Block: Block,
    Ret: Id,
    If: If,
    BuiltinType: Builtin.Compact,
    Underscore,
    Parens: Id,
    Record: Id.Index,

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

pub const Record = struct {
    const Kind = union(enum) {
        Struct,
    };

    kind: Kind,
    items: Item.Store.Slice,
};

arena: std.heap.ArenaAllocator.State = .{},
children: std.ArrayListUnmanaged(Record) = .{},
item_lookup: std.ArrayListUnmanaged(Item.Id) = .{},
items: Item.Store,
exprs: Expr.Store,
peak_sym_count: usize = undefined,
root: Record = undefined,

pub fn init() Ast {
    return .{
        .items = Item.Store.init(),
        .exprs = Expr.Store.init(),
    };
}

pub fn deinit(self: *Ast, alloc: std.mem.Allocator) void {
    self.arena.promote(alloc).deinit();
    self.children.deinit(alloc);
    self.item_lookup.deinit(alloc);
    self.items.deinit(alloc);
    self.exprs.deinit(alloc);
}

pub fn Printer(comptime W: type) type {
    return struct {
        const Self = @This();
        const WriteError = std.mem.Allocator.Error || W.Error;

        ast: *const Ast,
        writer: W,
        indent: usize,
        source: []const u8,
        exprs: Expr.Store.View = undefined,

        pub fn init(ast: *const Ast, writer: W, source: []const u8) Self {
            return .{ .ast = ast, .writer = writer, .indent = 0, .source = source };
        }

        pub fn print(self: *Self) WriteError!void {
            const view = self.ast.items.view(self.ast.root.items);
            for (view.query(.Func)) |item| {
                try self.printFunction(item);
                try self.writer.writeByte('\n');
            }
        }

        fn printFunction(self: *Self, func: Item.Func) WriteError!void {
            const prev = self.exprs;
            defer self.exprs = prev;
            self.exprs = self.ast.exprs.view(func.slice);

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

        fn printBlock(self: *Self, block: []Expr.Id) WriteError!void {
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

        fn printExpr(self: *Self, expr: Expr.Id) WriteError!void {
            return switch (self.exprs.get(expr)) {
                .Ident => |s| try self.printIdent(s),
                .Int => |s| try self.writer.print("{d}", .{s}),
                .Binary => |s| try self.printBinary(s),
                .Var => |s| try self.printVar(s),
                .Ret => |s| try self.printRet(s),
                .BuiltinType => |s| try Ast.Builtin.expand(s).print(self.writer),
                .Call => |s| try self.printCall(s),
                .Underscore => try self.writer.writeByte('_'),
                .Parens => |s| try self.printParens(s),
                .If => |s| try self.printIf(s),
                .Bool => |s| try self.writer.print("{any}", .{s}),
                else => try self.writer.print("{any}", .{expr}),
            };
        }

        fn printIf(self: *Self, expr: Expr.If) WriteError!void {
            try self.writer.writeAll("if (");
            try self.printExpr(expr.cond);
            try self.writer.writeAll(") ");
            try self.printExpr(expr.then);
            if (expr.els) |els| {
                try self.writer.writeAll(" else ");
                try self.printExpr(els);
            }
        }

        fn printParens(self: *Self, expr: Expr.Id) WriteError!void {
            try self.writer.writeByte('(');
            try self.printExpr(expr);
            try self.writer.writeByte(')');
        }

        fn printCall(self: *Self, expr: Expr.Call) WriteError!void {
            try self.printExpr(expr.callee);
            try self.writer.writeByte('(');
            for (expr.args, 0..) |arg, i| {
                try self.printExpr(arg);
                if (i + 1 != expr.args.len) try self.writer.writeAll(", ");
            }
            try self.writer.writeByte(')');
        }

        fn printRet(self: *Self, expr: Expr.Id) WriteError!void {
            try self.writer.writeAll("ret ");
            try self.printExpr(expr);
        }

        fn printVar(self: *Self, expr: Expr.Var) WriteError!void {
            try self.writer.writeAll("let ");
            try self.printIdent(expr.name);
            try self.writer.writeAll(" = ");
            try self.printExpr(expr.init);
        }

        fn printBinary(self: *Self, expr: Expr.Binary) WriteError!void {
            try self.printExpr(expr.lhs);
            try self.writer.writeByte(' ');
            try expr.op.print(self.writer);
            try self.writer.writeByte(' ');
            try self.printExpr(expr.rhs);
        }

        fn printIdent(self: *Self, ident: Ast.Ident) WriteError!void {
            try self.writer.writeAll(ident.slice(self.source));
        }

        fn printIndent(self: *Self) WriteError!void {
            for (0..self.indent * 4) |_| try self.writer.writeByte(' ');
        }
    };
}
