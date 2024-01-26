const std = @import("std");
const Lexer = @import("Lexer.zig");
const EnumList = @import("EnumList.zig");
const Parser = @import("Parser.zig");

const Self = @This();

pub const TypeKind = enum {
    Int,
    Void,
    Func,
};

pub const Type = union(TypeKind) {
    pub const Store = EnumList.Unmanaged(Type);
    pub const Id = EnumList.Id(TypeKind);

    pub const Int = packed struct(u16) {
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
    };

    pub const Builtin = union(enum) {
        Int: Int,
        Void,

        pub fn print(self: Builtin, writer: anytype) !void {
            switch (self) {
                .Int => |i| try i.print(writer),
                .Void => try writer.writeAll("void"),
            }
        }
    };

    pub const Func = struct {
        params: []Type.Id,
        ret: Type.Id,
    };

    Int: Int,
    Void,
    Func: Func,
};

pub const FuncMeta = struct {
    type: Type.Func,
    ast: Parser.Ast.Expr.Id,
};

pub const Module = struct {
    type_store: Type.Store,
    ast_types: EnumList.ShadowUnmanaged(Type.Id, Parser.Ast.Expr.Store),

    pub fn init(ast: *const Parser.Ast, alloc: std.mem.Allocator) !Self {
        return .{
            .type_store = Type.Store.init(),
            .ast_types = try EnumList.ShadowUnmanaged.init(ast.expr_store, alloc),
        };
    }
};

const Error = error{} || std.mem.Allocator.Error;

alloc: std.mem.Allocator,
scratch: *std.heap.ArenaAllocator,
ast: *const Parser.Ast,
types: *Module,

pub fn typechk(ast: *const Parser.Ast, alloc: std.mem.Allocator) Error!Module {
    var types = try Module.init(ast, alloc);
    var scratch = try std.heap.ArenaAllocator.init(alloc);
    defer scratch.deinit();

    var self = .{
        .alloc = alloc,
        .scratch = &scratch,
        .ast = ast,
        .types = &types,
    };

    try self.typecheck();

    return types;
}

fn typecheck(self: *Self) Error!void {
    for (self.ast.items.items) |item| {
        switch (item) {
            .Func => try self.typecheck_func(item),
        }
    }
}

test "parse int" {
    const passing = "u8 u16 u32 u64 i8 i16 i32 i64 u20";
    const failing = "u0 u u8u a f32 c20 u999999";

    var split = std.mem.split(u8, passing, " ");
    while (split.next()) |str| try std.testing.expect(Type.Int.parse(str) != null);

    split = std.mem.split(u8, failing, " ");
    while (split.next()) |str| try std.testing.expect(Type.Int.parse(str) == null);
}
