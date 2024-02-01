const std = @import("std");
const Typechk = @import("../Typechk.zig");
const Type = Typechk.Type;
const Types = Typechk.Module;
const Parser = @import("../Parser.zig");
const Ast = Parser.Ast;

pub const SigRegAlloc = struct {
    available: []u4,

    pub const general_args: SigRegAlloc = .{ .available = &[_]u4{ 5, 4, 2, 1, 8, 9 } };
    pub const simd_args: SigRegAlloc = .{ .available = &[_]u4{ 0, 1, 2, 3, 4, 5, 6, 7 } };
    pub const general_rets: SigRegAlloc = .{ .available = &[_]u4{ 0, 2 } };
    pub const simd_rets: SigRegAlloc = .{ .available = &[_]u4{ 0, 1 } };
};

pub const SigMemoryAlloc = struct {
    offset: usize = 0,

    pub fn alloc(self: *SigMemoryAlloc, size: usize) usize {
        const result = self.offset;
        self.offset += std.math.ceilPowerOfTwo(usize, size) catch unreachable;
        return result;
    }
};

pub const Reg = packed struct(u8) {
    pub const Set = u32;
    pub const Index = u5;

    pub const general_regs = makeSet(.{.{ 0, 15 }});
    pub const calee_saved = makeSet(.{ 3, 7, .{ 12, 15 } });
    pub const forbidden_registers = makeSet(.{6});
    pub const caller_saved = ~calee_saved & ~forbidden_registers;

    pub const biggest_reg = 128;
    pub const pointer_width = 64;
    pub const count = 1 << 5;

    pub const ret = cnst(false, 0);

    is_simd: bool,
    id: u4,
    padding: u3 = undefined,

    pub fn index(self: Reg) Index {
        return @as(Index, @intCast(self.id)) + @as(Index, @intFromBool(self.is_simd)) * 16;
    }

    pub fn fromIndex(i: Index) Reg {
        return .{
            .is_simd = i >= 16,
            .id = @intCast(i % 16),
        };
    }

    fn cnst(is_simd: bool, id: u4) Reg {
        return .{
            .is_simd = is_simd,
            .id = id,
        };
    }

    fn sizeToSizePowNormal(size: usize) u2 {
        std.debug.assert(size <= 8);
        return @intCast(std.math.log2_int(usize, size));
    }

    fn sizeToSizePowSimd(size: usize) u2 {
        std.debug.assert(size <= biggest_reg);
        return @intCast(std.math.log2_int(usize, size) - 7);
    }

    fn makeSet(ranges: anytype) Set {
        const fields = std.meta.fields(@TypeOf(ranges));
        var mask: Set = 0;
        inline for (fields) |f| {
            const value = @field(ranges, f.name);
            const start = if (f.type != comptime_int) value[0] else value;
            const end = if (f.type != comptime_int) value[1] else value;

            std.debug.assert(start <= end);
            std.debug.assert(end <= 32);
            mask |= ((one << (end + 1)) - 1) & ~((one << start) - 1);
        }
        return mask;
    }

    fn name(self: Reg, size: usize) []const u8 {
        const cield_size = std.math.ceilPowerOfTwo(usize, size) catch unreachable;
        const size_pow = if (self.is_simd)
            sizeToSizePowSimd(cield_size)
        else
            sizeToSizePowNormal(cield_size);

        return switch (self.is_simd) {
            true => switch (size_pow) {
                inline 0...2 => |sp| switch (self.id) {
                    inline else => |id| std.fmt.comptimePrint("{c}mm{d}", .{ "xyz"[sp], id }),
                },
                else => unreachable,
            },
            false => switch (self.id) {
                inline 0...3 => |id| switch (size_pow) {
                    inline else => |sp| &.{ "--er"[@max(sp, 2)], "acdb"[id], "lxxx"[sp] },
                },
                inline 4...7 => |id| switch (size_pow) {
                    inline else => |sp| .{"--er"[@max(sp, 2)]} ++
                        "sidispbp"[(id - 4) * 2 ..][0..2] ++ if (sp == 0) "l" else "",
                },
                inline 8...15 => |id| switch (size_pow) {
                    inline else => |sp| std.fmt.comptimePrint(
                        "r{d}{?c}",
                        .{ id, if (sp != 3) "bwd"[sp] else @as(?u8, null) },
                    ),
                },
            },
        };
    }
};

pub const ArgClass = enum {
    const max_sse_width = Reg.biggest_reg / Reg.pointer_width;

    const Result = struct {
        classes: [max_sse_width]ArgClass,
        count: u8,

        pub fn fromArray(cls: anytype) Result {
            const fields = std.meta.fields(@TypeOf(cls));
            comptime if (fields.len > 4) unreachable;

            var result: Result = undefined;
            result.count = fields.len;
            inline for (fields, result.classes[0..fields.len]) |f, *c| c.* = @field(cls, f.name);
            return result;
        }

        pub fn view(self: *const Result) []const ArgClass {
            return self.classes[0..self.count];
        }
    };

    Integer,
    Sse,
    SseUp,

    pub fn unify(self: ArgClass, other: ArgClass) ArgClass {
        return @enumFromInt(@min(@intFromEnum(self), @intFromEnum(other)));
    }

    pub fn fromType(ty: Type.Id, types: *const Types) ClassifyError!Result {
        return switch (types.store.get(ty)) {
            .Bool => Result.fromArray(.{.Integer}),
            .Int => |i| switch (i.bit_width) {
                0...64 => Result.fromArray(.{.Integer}),
                65...Reg.biggest_reg => |w| switch ((w + 63) / Reg.pointer_width) {
                    inline 2...(max_sse_width) => |j| Result.fromArray(
                        .{.Sse} ++ .{.SseUp} **
                            ((std.math.ceilPowerOfTwo(usize, j) catch unreachable) - 1),
                    ),
                    else => unreachable,
                },
                else => error.IsMemory,
            },
            else => std.debug.panic("TODO: {any}", .{ty}),
        };
    }
};

pub const ClassifyError = error{IsMemory};

const Iter = struct {
    used: Reg.Set,

    pub fn generalParams() Iter {
        return .{ .used = Reg.general_regs };
    }

    pub fn next(self: *Iter) ?u5 {
        const pos = @ctz(self.used);
        if (pos == Reg.count) return null;
        const bit = one << @intCast(pos);
        self.used &= ~bit;
        return pos;
    }

    pub fn nextBack(self: *Iter) ?u5 {
        var pos = @clz(self.used);
        if (pos == Reg.count) return null;
        pos = 15 - pos;
        const bit = one << @intCast(pos);
        self.used &= ~bit;
        return pos;
    }
};

const BaseInt = u32;
pub const Ref = std.meta.Int(.unsigned, @bitSizeOf(BaseInt) - @bitSizeOf(Reg));
pub const Spill = packed struct(BaseInt) {
    reg: Reg,
    spill: Ref,
};

const Self = @This();

const one: Reg.Set = 1;

// 1s mean allocated
allocated: Reg.Set = Reg.forbidden_registers,
used: Reg.Set = 0,
locations: [Reg.count]?Ref = [_]?Ref{null} ** Reg.count,
spill_ring: u4 = 0,

fn allocGeneral(self: *Self, to: Ref) ?Reg {
    return self.allocFiltered(to, Reg.general_regs);
}

fn allocFiltered(self: *Self, to: Ref, filter: Reg.Set) ?Reg {
    var pos = @clz(~(self.allocated | ~filter));
    if (pos == Reg.count) return null;
    pos = 31 - pos;
    const bit = one << @intCast(pos);
    self.allocated |= bit;
    self.used |= bit;
    self.locations[pos] = to;
    return Reg.fromIndex(@intCast(pos));
}

pub fn allocSpecific(self: *Self, to: Ref, reg: Reg) ?Ref {
    const pos = reg.index();
    const bit = one << @intCast(pos);
    self.allocated |= bit;
    self.used |= bit;
    defer self.locations[pos] = to;
    return self.locations[pos];
}

pub fn free(self: *Self, reg: Reg) void {
    const pos = reg.index();
    const bit = one << @intCast(pos);
    std.debug.assert(self.allocated & bit != 1);
    self.allocated &= ~bit;
    self.locations[pos] = null;
}

pub fn spill(self: *Self, to: Ref) Spill {
    const offset = Reg;
    _ = offset;
    defer self.locations[self.spill_ring] = to;
    return .{ .reg = @enumFromInt(self.spill_ring), .spill = self.locations[self.spill_ring].? };
}

pub fn restore(self: *Self, reg: Reg, from: Ref) void {
    const pos = @intFromEnum(reg);
    self.locations[pos] = from;
}

pub fn usedIter(self: *const Self) Iter {
    return .{ .used = self.used };
}

test "arg class" {
    const ast = Ast.init();
    var types = try Types.init(std.testing.allocator, &ast);
    defer types.deinit(std.testing.allocator);

    const result = try ArgClass.fromType(Type.usize_lit, &types);
    try std.testing.expectEqualSlices(ArgClass, &.{.Integer}, result.view());

    const result2 = ArgClass.unify(.Integer, .Sse);
    try std.testing.expectEqual(result2, .Integer);
}

test "reg name" {
    try std.testing.expectEqualStrings(Reg.ret.name(8), "rax");
}

test "reg alloc" {
    var alloc: Self = .{};
    const dummy_ref: Ref = 0;

    try std.testing.expectEqual(alloc.allocGeneral(dummy_ref).?.index(), 15);
    try std.testing.expectEqual(alloc.allocGeneral(dummy_ref).?.index(), 14);
    try std.testing.expectEqual(alloc.allocSpecific(dummy_ref, Reg.cnst(false, 14)).?, dummy_ref);
}
