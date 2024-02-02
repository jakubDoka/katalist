const std = @import("std");
const Lexer = @import("Lexer.zig");
const EnumList = @import("EnumList.zig");
const Parser = @import("Parser.zig");
const Ast = Parser.Ast;

const Self = @This();

pub const TypeKind = enum {
    Void,
    Type,
    Decl,
    Bool,
    Never,
    Int,
};

pub const Type = union(TypeKind) {
    pub const Store = EnumList.Unmanaged(Type);
    pub const Id = EnumList.Id(TypeKind);
    pub const Builtin = Parser.Builtin;
    pub const Int = Parser.Int;

    pub const type_lit = Type.encode(.Type).?;
    pub const void_lit = Type.encode(.Void).?;
    pub const bool_lit = Type.encode(.Bool).?;
    pub const never_lit = Type.encode(.Never).?;
    pub const ctint_lit = Type.encode(.{ .Int = Int.Ctint }).?;
    pub const usize_lit = Type.encode(.{ .Int = Int.Usize }).?;
    pub const decl_lit = Type.encode(.Decl).?;

    pub const Func = struct {
        params: []Ast.Expr.Id,
        ret: Ast.Expr.Id,
    };

    Void,
    Type,
    Decl,
    Bool,
    Never,
    Int: Int,

    pub fn fromBuiltin(self: Builtin) Type.Id {
        return Type.encode(switch (self) {
            .Int => |i| .{ .Int = i },
            inline else => |_, t| @unionInit(Type, @tagName(t), {}),
        }).?;
    }

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

        if (a == .Never) return other;
        if (b == .Never) return self;

        if (a == .Int and b == .Int) {
            if (a.Int.isCt()) return other;
            if (b.Int.isCt()) return self;
        }

        return null;
    }
};

pub const Value = struct {
    pub const void_lit = Value{};
    pub const never_lit = Value{ .type = Type.never_lit };

    pub const Data = union {
        int: u64,
        bool: bool,
        pointer: *Value,
        type: Type.Id,
        decl: Ast.Item.Id,
        void: void,
    };

    type: Type.Id = Type.void_lit,
    is_runtime: bool = false,
    is_mutable: bool = false,
    data: Data = .{ .void = {} },

    pub fn ty(typ: Type.Id) Value {
        return .{
            .type = Type.type_lit,
            .data = .{ .type = typ },
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
            .data = self.data.pointer.data,
        };
    }

    pub fn fromInlineAst(builtin: Ast.Expr.Id) ?Value {
        const ia = Ast.Expr.Id.decode(Ast.Expr, builtin) orelse return null;
        switch (ia) {
            .BuiltinType => |b| return ty(Type.Builtin.expand(b).asType()),
            .Bool => |b| return .{ .type = Type.bool_lit, .data = .{ .bool = b } },
            else => return null,
        }
    }
};

pub const Module = struct {
    const AstStore = EnumList.ShadowUnmanaged(Value, Parser.Ast.Expr.Store);

    store: Type.Store,
    ast: AstStore,
    reached_functions: []Parser.Ast.Item.Id = &.{},
    entry: ?usize = null,

    pub fn init(alloc: std.mem.Allocator, ast: *const Parser.Ast) !Module {
        var func_count: usize = 0;
        for (ast.items.items) |item| func_count += @intFromBool(item.tag == .Func);

        return .{
            .store = Type.Store.init(),
            .ast = try AstStore.init(&ast.exprs, alloc),
        };
    }

    pub fn deinit(self: *Module, alloc: std.mem.Allocator) void {
        self.store.deinit(alloc);
        self.ast.deinit(alloc);
        alloc.free(self.reached_functions);
    }

    pub fn getValue(self: *const Module, expr: Parser.Ast.Expr.Id) Value {
        return self.ast.get(expr) orelse Value.fromInlineAst(expr).?;
    }

    pub fn bitSizeOf(self: *const Module, ty: Type.Id) u12 {
        return switch (self.store.get(ty)) {
            .Int => |i| @intCast(i.bit_width),
            .Bool => 1,
            else => 0,
        };
    }
};

const Scope = struct {
    pub const Frame = struct {
        total: usize,
    };

    pub const Symbol = struct {
        is_mutable: bool = false,
        value: Value,
    };

    symbols: []Symbol,
    ret: ?Type.Id = null,
    ret_value: ?Value = null,

    pub fn init(buffer: []Symbol) Scope {
        return .{ .symbols = buffer[0..0] };
    }

    pub fn add(self: *Scope, sym: Symbol) Error!usize {
        self.symbols.len += 1;
        self.symbols[self.symbols.len - 1] = sym;
        return self.symbols.len - 1;
    }

    pub fn find(self: *Scope, ident: Ast.Ident) ?*Symbol {
        if (ident.unordered) return null;
        return &self.symbols[ident.index];
    }

    pub fn pushFrame(self: *Scope) Frame {
        return .{ .total = self.symbols.len };
    }

    pub fn popFrame(self: *Scope, frame: Frame) void {
        self.symbols.len = frame.total;
    }
};

const FuncFlags = packed struct {
    computed_signature: bool = false,
    computed_body: bool = false,
};

pub const Error = error{} || std.mem.Allocator.Error;
const InnerError = error{Returned} || Error;

alloc: std.mem.Allocator,
scratch: *std.heap.ArenaAllocator,
ast: *const Parser.Ast,
types: *Module,
scope: *Scope,
to_check: std.ArrayList(Parser.Ast.Item.Id),
func_set: []FuncFlags = &.{},
source: []const u8,

pub fn check(alloc: std.mem.Allocator, ast: *const Parser.Ast, source: []const u8) Error!Module {
    var types = try Module.init(alloc, ast);

    var scratch = std.heap.ArenaAllocator.init(alloc);
    defer scratch.deinit();

    const scope_buffer = try alloc.alloc(Scope.Symbol, ast.peak_sym_count);
    defer alloc.free(scope_buffer);
    var scope = Scope.init(scope_buffer);

    var self = Self{
        .alloc = alloc,
        .scratch = &scratch,
        .ast = ast,
        .types = &types,
        .scope = &scope,
        .to_check = std.ArrayList(Parser.Ast.Item.Id).init(alloc),
        .source = source,
    };

    defer self.to_check.deinit();

    try self.checkFile();

    return types;
}

fn checkFile(self: *Self) Error!void {
    for (self.ast.items.items) |item| {
        const ident = switch (self.ast.items.get(item)) {
            .Func => |f| f.name,
        };

        if (std.mem.eql(u8, ident.slice(self.source), "main")) try self.to_check.append(item);
    }

    if (self.to_check.items.len == 0) @panic("todo");

    self.func_set = try self.alloc.alloc(FuncFlags, self.ast.items.items.len);
    for (self.func_set) |*f| f.* = .{};
    defer self.alloc.free(self.func_set);

    while (self.to_check.popOrNull()) |id| {
        switch (self.ast.items.get(id)) {
            .Func => |f| try self.checkFunc(f, id.index),
        }
    }

    var reached_function_count: usize = 0;
    for (self.func_set) |f| reached_function_count += @intFromBool(f.computed_body);
    self.types.reached_functions = try self.alloc.alloc(Parser.Ast.Item.Id, reached_function_count);

    var i: usize = 0;
    for (self.func_set, 0..) |f, j| if (f.computed_body) {
        self.types.reached_functions[i] = .{ .tag = .Func, .index = @intCast(j) };
        i += 1;
    };
}

fn checkSignature(self: *Self, func: Ast.Item.Func, id: usize) InnerError!Value {
    if (self.func_set[id].computed_signature) {
        for (func.params) |param| {
            const value = self.types.getValue(param.type);
            _ = try self.scope.add(.{ .value = Value.rt(value.data.type) });
        }
        return self.types.getValue(func.ret);
    }

    for (func.params) |param| {
        const value = try self.checkExpr(Type.type_lit, param.type);
        _ = try self.scope.add(.{ .value = Value.rt(value.data.type) });
    }
    const res = try self.checkExpr(Type.type_lit, func.ret);

    try self.to_check.append(.{ .tag = .Func, .index = @intCast(id) });
    self.func_set[id].computed_signature = true;
    return res;
}

fn checkFunc(self: *Self, func: Ast.Item.Func, id: usize) Error!void {
    const frame = self.scope.pushFrame();
    const ret = self.checkSignature(func, id) catch |e| switch (e) {
        InnerError.Returned => @panic("todo"),
        else => |er| return er,
    };
    self.scope.ret = ret.data.type;
    self.checkBlock(func.body) catch |e| switch (e) {
        InnerError.Returned => {},
        else => |er| return er,
    };
    self.scope.popFrame(frame);

    self.func_set[id].computed_body = true;
}

fn checkExpr(self: *Self, expected: ?Type.Id, expr: Parser.Ast.Expr.Id) InnerError!Value {
    errdefer if (self.types.ast.at(expr)) |slot| {
        slot.* = Value.never_lit;
    };

    var val = switch (self.ast.exprs.get(expr)) {
        .BuiltinType => |b| Value.ty(Type.Builtin.expand(b).asType()),
        .Int => |i| Value{ .type = expected orelse Type.ctint_lit, .data = .{ .int = i } },
        .Bool => |b| Value{ .type = Type.bool_lit, .data = .{ .bool = b } },
        .Ret => |r| try self.checkRet(r),
        .Binary => |o| try self.checkBinary(o),
        .Ident => |i| try self.checkIdent(i),
        .Var => |v| try self.checkVar(v),
        .Call => |c| try self.checkCall(c),
        .If => |i| try self.checkIf(expected, i),
        .Parens => |p| try self.checkExpr(expected, p),
        inline else => |val, tag| std.debug.panic("todo: {any} {any}", .{ tag, val }),
    };

    if (expected) |e| val.type = Type.unify(e, val.type) orelse
        std.debug.panic("todo: {any} {any}", .{ e, val.type });

    if (self.types.ast.at(expr)) |slot| slot.* = val;

    return val;
}

fn checkIf(self: *Self, expected: ?Type.Id, i: Parser.Ast.Expr.If) InnerError!Value {
    const cond = try self.checkExpr(Type.bool_lit, i.cond);

    if (!cond.is_runtime) {
        if (cond.data.bool) return try self.checkExpr(expected, i.then);
        if (i.els) |e| return try self.checkExpr(expected, e);
        return Value{};
    }

    var then = self.checkExpr(expected, i.then) catch Value.never_lit;
    var els = if (i.els) |e| self.checkExpr(then.type, e) catch Value.never_lit else null;
    then.type = if (els) |e| Type.unify(then.type, e.type) orelse @panic("todo") else then.type;

    if (then.type.eql(Type.never_lit) and els != null) return error.Returned;

    return Value.rt(then.type);
}

fn checkCall(self: *Self, c: Parser.Ast.Expr.Call) InnerError!Value {
    const decl = (try self.checkExpr(Type.decl_lit, c.callee)).data.decl;

    if (decl.tag != .Func) @panic("todo");
    const func = self.ast.items.get(decl).Func;

    const frame = self.scope.pushFrame();
    const ret = (try self.checkSignature(func, decl.index)).data.type;
    self.scope.popFrame(frame);

    if (func.params.len != c.args.len) @panic("todo");

    for (func.params, c.args) |param, arg| {
        const param_type = self.types.getValue(param.type);
        _ = try self.checkExpr(param_type.data.type, arg);
    }

    return Value.rt(ret);
}

fn checkVar(self: *Self, v: Parser.Ast.Expr.Var) InnerError!Value {
    const ty = if (v.type) |t| (try self.checkExpr(Type.type_lit, t)).data.type else null;
    var value = try self.checkExpr(ty, v.init);
    value.is_runtime = !v.is_const;
    if (value.type.eql(Type.ctint_lit) and value.is_runtime) @panic("todo");

    _ = try self.scope.add(.{ .is_mutable = !v.is_const, .value = value });
    return Value{ .is_runtime = value.is_runtime };
}

fn checkIdent(self: *Self, i: Parser.Ast.Ident) InnerError!Value {
    var sym = self.scope.find(i) orelse return self.checkUnorderedIdent(i);
    if (!sym.is_mutable) return sym.value;
    const data: Value.Data = if (sym.value.is_runtime) .{ .void = {} } else .{ .pointer = &sym.value };
    return .{
        .type = sym.value.type,
        .is_mutable = true,
        .is_runtime = sym.value.is_runtime,
        .data = data,
    };
}

fn checkUnorderedIdent(self: *Self, i: Parser.Ast.Ident) InnerError!Value {
    std.debug.assert(i.unordered);
    const decl = self.ast.items.items[i.index];
    return .{ .type = Type.decl_lit, .data = .{ .decl = decl } };
}

fn checkRet(self: *Self, r: Parser.Ast.Expr.Id) InnerError!Value {
    const ret = self.scope.ret orelse @panic("todo");
    const value = try self.checkExpr(ret, r);

    if (!value.is_runtime) if (self.types.ast.at(r)) |slot| {
        slot.* = value.ensureLoaded();
    };

    if (self.scope.ret_value) |*v| v.is_runtime = true else {
        self.scope.ret_value = value;
    }

    return InnerError.Returned;
}

fn checkBinary(self: *Self, b: Parser.Ast.Expr.Binary) InnerError!Value {
    return switch (b.op) {
        .Add, .Sub, .Eq, .Ne, .Gt, .Lt, .Ge, .Le => try self.checkMathOp(b),
        .Assign => try self.checkAssign(b),
    };
}

fn checkMathOp(self: *Self, op: Parser.Ast.Expr.Binary) InnerError!Value {
    const lhs = try self.checkExpr(null, op.lhs);
    const rhs = try self.checkExpr(lhs.type, op.rhs);
    const ty = switch (op.op) {
        .Add, .Sub => lhs.type,
        .Eq, .Ne, .Gt, .Lt, .Ge, .Le => Type.bool_lit,
        else => unreachable,
    };

    if (lhs.is_runtime or rhs.is_runtime) {
        if (!lhs.type.eql(rhs.type))
            (self.types.ast.at(op.lhs) orelse @panic("todo")).* = Value.rt(ty);
        return Value.rt(ty);
    }

    const lhs_val = lhs.ensureLoaded().data;
    const rhs_val = rhs.ensureLoaded().data;
    return switch (op.op) {
        .Add => Value{ .type = ty, .data = .{ .int = lhs_val.int + rhs_val.int } },
        .Sub => Value{ .type = ty, .data = .{ .int = lhs_val.int - rhs_val.int } },
        .Eq => Value{ .type = ty, .data = .{ .bool = lhs_val.int == rhs_val.int } },
        .Ne => Value{ .type = ty, .data = .{ .bool = lhs_val.int != rhs_val.int } },
        .Gt => Value{ .type = ty, .data = .{ .bool = lhs_val.int > rhs_val.int } },
        .Lt => Value{ .type = ty, .data = .{ .bool = lhs_val.int < rhs_val.int } },
        .Ge => Value{ .type = ty, .data = .{ .bool = lhs_val.int >= rhs_val.int } },
        .Le => Value{ .type = ty, .data = .{ .bool = lhs_val.int <= rhs_val.int } },
        else => unreachable,
    };
}

fn checkAssign(self: *Self, a: Parser.Ast.Expr.Binary) InnerError!Value {
    if (a.lhs.tag == .Underscore) {
        _ = try self.checkExpr(null, a.rhs);
        return Value{};
    }

    const lhs = try self.checkExpr(null, a.lhs);
    const rhs = try self.checkExpr(lhs.type, a.rhs);

    if (!lhs.is_mutable) @panic("todo");
    if (!lhs.is_runtime) if (rhs.is_runtime) {
        lhs.data.pointer.is_runtime = true;
        lhs.data.pointer.type = Type.unify(lhs.data.pointer.type, rhs.type) orelse @panic("todo");
        return Value.rt(Type.void_lit);
    } else {
        lhs.data.pointer.* = rhs.ensureLoaded();
    } else {
        return Value.rt(Type.void_lit);
    }

    return Value{};
}

fn checkBlock(self: *Self, block: Parser.Ast.Expr.Block) InnerError!void {
    const frame = self.scope.pushFrame();
    for (block) |stmt| _ = try self.checkExpr(Type.void_lit, stmt);
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
        \\fn main(a: usize, b: usize) usize {
        \\    var foo: usize = 1 + 1;
        \\    _ = 1;
        \\    foo = 2;
        \\    foo = a;
        \\    return a + b + foo;
        \\}
    ;

    const alloc = std.testing.allocator;

    var ast = try Parser.parse(alloc, src);
    defer ast.deinit(alloc);

    for (ast.errors.items) |err| std.log.warn("{any}", .{err});
    try std.testing.expect(ast.errors.items.len == 0);

    var types = try check(alloc, &ast, src);
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
