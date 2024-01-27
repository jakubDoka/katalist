const std = @import("std");
const Lexer = @import("Lexer.zig");
const EnumList = @import("EnumList.zig");
const Parser = @import("Parser.zig");
const Ast = Parser.Ast;

const Self = @This();

pub const TypeKind = enum {
    Int,
    Void,
    Type,
    Func,
    Pointer,
};

pub const Type = union(TypeKind) {
    pub const Store = EnumList.Unmanaged(Type);
    pub const Id = EnumList.Id(TypeKind);
    pub const type_lit = Type.encode(.Type).?;
    pub const void_lit = Type.encode(.Void).?;
    pub const ctint_lit = Type.encode(.{ .Int = Int.Ctint }).?;

    pub const Int = packed struct(u16) {
        pub const Usize = Int{ .signed = false, .bit_width = 64 };
        pub const Isize = Int{ .signed = true, .bit_width = 64 };
        pub const Ctint = Int{ .signed = true, .bit_width = ~@as(u15, 0) };

        signed: bool,
        bit_width: u15,

        pub fn parse(str: []const u8) ?Int {
            if (str.len < 2) return null;

            if (std.mem.eql(u8, str, "usize")) return .{ .signed = false, .bit_width = 64 };

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
            return self.bit_width == ~@as(u15, 0);
        }
    };

    pub const Builtin = union(enum) {
        Int: Int,
        Void,
        Type,

        pub fn print(self: Builtin, writer: anytype) !void {
            switch (self) {
                .Int => |i| try i.print(writer),
                .Void => try writer.writeAll("void"),
                .Type => try writer.writeAll("type"),
            }
        }

        pub fn asType(self: Builtin) Type.Id {
            return Type.encode(switch (self) {
                .Int => |i| .{ .Int = i },
                .Void => .Void,
                .Type => .Type,
            }).?;
        }
    };

    pub const Func = struct {
        params: []Ast.Expr.Id,
        ret: Ast.Expr.Id,
    };

    Int: Int,
    Void,
    Type,
    Func: Func,
    Pointer: Id,

    pub fn encode(self: Type) ?Id {
        return Id.encode(self);
    }

    pub fn decode(id: Id) ?Type {
        return Id.decode(Type, id);
    }

    pub fn unify(self: Id, other: Id) ?Id {
        if (Id.eql(self, other)) return self;

        const a = decode(self) orelse return null;
        const b = decode(other) orelse return null;

        if (a == .Int and b == .Int) {
            if (a.Int.isCt()) return other;
            if (b.Int.isCt()) return self;
        }

        return null;
    }
};

pub const Value = struct {
    const void_lit = Value{};

    type: Type.Id = Type.void_lit,
    is_runtime: bool = false,
    is_mutable: bool = false,
    value: union {
        int: u64,
        pointer: *Value,
        type: Type.Id,
        void: void,
    } = .{ .void = {} },

    pub fn ty(typ: Type.Id) Value {
        return .{
            .type = Type.type_lit,
            .value = .{ .type = typ },
        };
    }

    pub fn rt(typ: Type.Id) Value {
        return .{
            .type = typ,
            .is_runtime = true,
        };
    }

    pub fn ensureLoaded(self: Value) Value {
        std.debug.assert(!self.is_runtime);
        if (!self.is_mutable) return self;
        return .{
            .type = self.type,
            .value = self.value.pointer.*.value,
        };
    }
};

pub const Module = struct {
    const AstStore = EnumList.ShadowUnmanaged(Value, Parser.Ast.Expr.Store);

    store: Type.Store,
    ast: AstStore,

    pub fn init(ast: *const Parser.Ast, alloc: std.mem.Allocator) !Module {
        return .{
            .store = Type.Store.init(),
            .ast = try AstStore.init(&ast.expr_store, alloc),
        };
    }

    pub fn deinit(self: *Module, alloc: std.mem.Allocator) void {
        self.store.deinit(alloc);
        self.ast.deinit(alloc);
    }
};

const Scope = struct {
    pub const Frame = usize;
    pub const Symbol = struct {
        ident: Ast.Ident,
        is_mutable: bool = false,
        value: Value,
    };

    alloc: std.mem.Allocator,
    symbols: std.SegmentedList(Symbol, 8),
    ret: ?Type.Id = null,
    ret_value: ?Value = null,

    pub fn init(alloc: std.mem.Allocator) Scope {
        return .{
            .alloc = alloc,
            .symbols = .{},
        };
    }

    pub fn deinit(self: *Scope) void {
        self.symbols.deinit(self.alloc);
    }

    pub fn add(self: *Scope, sym: Symbol) Error!void {
        (try self.symbols.addOne(self.alloc)).* = sym;
    }

    pub fn find(self: *Scope, ident: Ast.Ident) ?*Symbol {
        for (0..self.symbols.len) |i| {
            const sym = self.symbols.at(self.symbols.len - i - 1);
            if (std.meta.eql(sym.ident, ident)) return sym;
        }
        return null;
    }

    pub fn pushFrame(self: *Scope) Frame {
        return self.symbols.len;
    }

    pub fn popFrame(self: *Scope, frame: Frame) void {
        self.symbols.len = frame;
    }
};

pub const Error = error{} || std.mem.Allocator.Error;
const InnerError = error{
    Returned,
} || Error;

alloc: std.mem.Allocator,
scratch: *std.heap.ArenaAllocator,
ast: *const Parser.Ast,
types: *Module,
scope: *Scope,

pub fn typechk(ast: *const Parser.Ast, alloc: std.mem.Allocator) Error!Module {
    var types = try Module.init(ast, alloc);
    var scratch = std.heap.ArenaAllocator.init(alloc);
    defer scratch.deinit();
    var scope = Scope.init(alloc);
    defer scope.deinit();

    var self = Self{
        .alloc = alloc,
        .scratch = &scratch,
        .ast = ast,
        .types = &types,
        .scope = &scope,
    };

    try self.typechkFile();

    return types;
}

fn typechkFile(self: *Self) Error!void {
    for (self.ast.items.items) |item| {
        switch (self.ast.item_store.get(item)) {
            .Func => |f| try self.typechkFunc(f),
        }
    }
}

fn typechkFunc(self: *Self, func: Parser.Ast.Item.Func) Error!void {
    const frame = self.scope.pushFrame();
    for (func.params) |param| {
        const value = self.typechkExpr(Type.type_lit, param.type) catch @panic("todo");
        try self.scope.add(.{ .ident = param.name, .value = Value.rt(value.value.type) });
    }

    const ret = self.typechkExpr(Type.type_lit, func.ret) catch @panic("todo");
    self.scope.ret = ret.value.type;
    self.typechkBlock(func.body) catch |e| switch (e) {
        InnerError.Returned => {},
        else => |er| return er,
    };
    self.scope.popFrame(frame);
}

fn typechkExpr(self: *Self, expected: ?Type.Id, expr: Parser.Ast.Expr.Id) InnerError!Value {
    const val = switch (self.ast.expr_store.get(expr)) {
        .BuiltinType => |b| Value.ty(b.asType()),
        .Int => |i| Value{ .type = Type.ctint_lit, .value = .{ .int = i } },
        .Ret => |r| {
            const ret = self.scope.ret orelse @panic("todo");
            if (self.scope.ret_value) |*v| v.is_runtime = true else {
                self.scope.ret_value = try self.typechkExpr(ret, r);
            }
            return InnerError.Returned;
        },
        .Binary => |o| switch (o.op) {
            .Add, .Sub => b: {
                const lhs = try self.typechkExpr(expected, o.lhs);
                const rhs = try self.typechkExpr(lhs.type, o.rhs);
                const ty = rhs.type;

                if (lhs.is_runtime or rhs.is_runtime) break :b Value.rt(ty);

                break :b switch (o.op) {
                    .Add => Value{ .type = ty, .value = .{ .int = lhs.value.int + rhs.value.int } },
                    .Sub => Value{ .type = ty, .value = .{ .int = lhs.value.int - rhs.value.int } },
                    else => unreachable,
                };
            },
            .Assign => b: {
                if (o.lhs.tag == .Underscore) {
                    _ = try self.typechkExpr(null, o.rhs);
                    break :b Value{};
                }

                const lhs = try self.typechkExpr(null, o.lhs);
                const rhs = try self.typechkExpr(lhs.type, o.rhs);

                if (!lhs.is_mutable) @panic("todo");
                if (!lhs.is_runtime and rhs.is_runtime) lhs.value.pointer.is_runtime = true;
                if (!lhs.is_runtime or !rhs.is_runtime) lhs.value.pointer.* = rhs.ensureLoaded();

                break :b Value{};
            },
        },
        .Ident => |i| b: {
            const sym = self.scope.find(i) orelse @panic("todo");
            if (sym.value.is_runtime) break :b sym.value;
            if (!sym.is_mutable) break :b sym.value;
            break :b Value{ .type = sym.value.type, .is_mutable = true, .value = .{ .pointer = &sym.value } };
        },
        .Var => |v| b: {
            const value = try self.typechkExpr(null, v.init);
            try self.scope.add(.{ .ident = v.name, .is_mutable = !v.is_const, .value = value });
            break :b Value.void_lit;
        },
        inline else => |val, tag| std.debug.panic("todo: {any} {any}", .{ tag, val }),
    };

    if (expected) |e| if (Type.unify(e, val.type) == null) std.debug.panic("todo: {any} {any}", .{ e, val.type });
    if (self.types.ast.at(expr)) |slot| slot.* = val;

    return val;
}

fn typechkBlock(self: *Self, block: Parser.Ast.Expr.Block) InnerError!void {
    const frame = self.scope.pushFrame();
    for (block) |stmt| _ = try self.typechkExpr(Type.void_lit, stmt);
    self.scope.popFrame(frame);
}

fn addType(self: *Self, ty: Type) !Type.Id {
    return try self.types.store.push(self.alloc, ty);
}

fn addPtr(self: *Self, ty: Type.Id) !Type.Id {
    return try self.types.store.find_or_push(self.alloc, .{ .Pointer = ty });
}

test "sanity" {
    const src =
        \\fn foo(a: usize, b: usize) usize {
        \\    var foo = 1 + 1;
        \\    _ = 1;
        \\    foo = 2;
        \\    return a + b + foo;
        \\}
    ;

    const alloc = std.testing.allocator;

    var ast = try Parser.parse(alloc, src);
    defer ast.deinit(alloc);

    for (ast.errors.items) |err| std.log.warn("{any}", .{err});
    try std.testing.expect(ast.errors.items.len == 0);

    var types = try typechk(&ast, alloc);
    defer types.deinit(alloc);
}

test "parse int" {
    const passing = "u8 u16 u32 u64 i8 i16 i32 i64 u20";
    const failing = "u0 u u8u a f32 c20 u999999";

    var split = std.mem.split(u8, passing, " ");
    while (split.next()) |str| try std.testing.expect(Type.Int.parse(str) != null);

    split = std.mem.split(u8, failing, " ");
    while (split.next()) |str| try std.testing.expect(Type.Int.parse(str) == null);
}
