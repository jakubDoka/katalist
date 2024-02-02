const std = @import("std");
const Type = std.builtin.Type;

const BackingInt = u32;
const Len = u16;

const PackedSlice = packed struct(BackingInt) {
    const Self = @This();

    index: u20 = 0,
    len: u12 = 0,

    fn fromRange(start: usize, end: usize) Self {
        return .{ .index = @intCast(start), .len = @intCast(end - start) };
    }

    fn slice(self: Self, comptime E: type, data: []const E) []const E {
        return data[self.index .. self.index + self.len];
    }
};

fn isInlined(comptime Tag: type, comptime T: type) bool {
    return @bitSizeOf(T) < @bitSizeOf(BackingInt) - @bitSizeOf(Tag);
}

fn UnionAsPtr(comptime T: type) type {
    comptime var meta = @typeInfo(T).Union;
    comptime var fields = meta.fields[0..meta.fields.len].*;
    for (&fields) |*field| {
        if (isInlined(meta.tag_type.?, field.type)) continue;
        field.type = *field.type;
    }
    meta.fields = &fields;
    meta.decls = &.{};
    return @Type(.{ .Union = meta });
}

fn UnionStorage(comptime T: type, comptime field_map: fn (ty: type) type) type {
    const meta = @typeInfo(T).Union;
    const Tag = meta.tag_type.?;

    comptime var fields: [meta.fields.len]Type.StructField = undefined;
    comptime var kept = 0;
    for (meta.fields) |field| {
        if (isInlined(Tag, field.type)) continue;

        const Ty = field_map(field.type);
        fields[kept] = .{
            .name = field.name,
            .type = Ty,
            .alignment = @alignOf(Ty),
            .default_value = null,
            .is_comptime = false,
        };
        kept += 1;
    }

    return @Type(.{ .Struct = .{
        .fields = fields[0..kept],
        .layout = Type.ContainerLayout.Auto,
        .decls = &.{},
        .backing_integer = null,
        .is_tuple = false,
    } });
}

fn UnionPackedSlice(comptime T: type) type {
    const field_map = struct {
        fn lane(comptime _: type) type {
            return PackedSlice;
        }
    }.lane;
    return UnionStorage(T, field_map);
}

fn UnionView(comptime T: type) type {
    const field_map = struct {
        fn lane(comptime V: type) type {
            return []const V;
        }
    }.lane;
    return struct {
        const Index = Id(std.meta.Tag(T));
        const Self = @This();
        const View = UnionStorage(T, field_map);

        view: View,

        pub fn get(self: *const Self, index: Index) T {
            return switch (index.tag) {
                inline else => |tag| {
                    if (!@hasField(View, @tagName(tag))) return Index.decodeStatic(T, tag, index.index).?;
                    const value = @field(self.view, @tagName(tag))[index.index];
                    return @unionInit(T, @tagName(tag), value);
                },
            };
        }

        pub fn query(self: *const Self, comptime tag: std.meta.Tag(T)) []const std.meta.FieldType(T, tag) {
            return @field(self.view, @tagName(tag));
        }
    };
}

fn UnionLen(comptime T: type) type {
    const field_map = struct {
        fn lane(comptime _: type) type {
            return Len;
        }
    }.lane;
    return UnionStorage(T, field_map);
}

fn UnionCheckpoint(comptime T: type) type {
    const field_map = struct {
        fn lane(comptime _: type) type {
            return usize;
        }
    }.lane;
    return UnionStorage(T, field_map);
}

pub fn Id(comptime T: type) type {
    const Idx = @Type(.{ .Int = .{
        .signedness = std.builtin.Signedness.unsigned,
        .bits = @bitSizeOf(BackingInt) - @bitSizeOf(T),
    } });

    return packed struct(BackingInt) {
        pub const Index = Idx;

        tag: T,
        index: Index,

        pub fn eql(self: @This(), other: @This()) bool {
            return self.tag == other.tag and self.index == other.index;
        }

        pub fn encode(data: anytype) ?@This() {
            if (@TypeOf(data) == T) {
                return .{ .tag = data, .index = 0 };
            }

            return switch (data) {
                inline else => |val, tag| encodeStatic(tag, val),
            };
        }

        pub fn encodeStatic(comptime tag: T, data: anytype) ?@This() {
            if (@sizeOf(@TypeOf(data)) == 0) {
                return .{ .tag = tag, .index = 0 };
            }

            if (comptime isInlined(@TypeOf(tag), @TypeOf(data))) {
                const Int = std.meta.Int(.unsigned, @bitSizeOf(@TypeOf(data)));
                return .{ .tag = tag, .index = @intCast(@as(Int, @bitCast(data))) };
            }

            return null;
        }

        pub fn decode(comptime D: type, self: @This()) ?D {
            return switch (self.tag) {
                inline else => |tag| decodeStatic(D, tag, self.index),
            };
        }

        pub fn decodeStatic(comptime D: type, comptime tag: T, index: Index) ?D {
            const field = std.meta.fieldInfo(D, tag);

            if (@sizeOf(field.type) == 0) {
                return @unionInit(D, field.name, {});
            }

            if (comptime isInlined(@TypeOf(tag), field.type)) {
                const Int = std.meta.Int(.unsigned, @bitSizeOf(field.type));
                return @unionInit(D, field.name, @bitCast(@as(Int, @intCast(index))));
            }

            return null;
        }
    };
}

pub fn Unmanaged(comptime T: type) type {
    return struct {
        const Self = @This();

        pub const Storage = UnionStorage(T, std.ArrayListUnmanaged);
        pub const Slice = UnionPackedSlice(T);
        pub const Len = UnionLen(T);
        pub const Checkpoint = UnionCheckpoint(T);
        pub const View = UnionView(T);
        pub const Index = Id(std.meta.Tag(T));
        pub const AsPtr = UnionAsPtr(T);
        pub const Item = T;

        storage: Storage,

        pub fn init() Self {
            var storage: Storage = undefined;
            inline for (std.meta.fields(Storage)) |field| @field(storage, field.name) = .{};
            return .{ .storage = storage };
        }

        pub fn deinit(self: *Self, alloc: std.mem.Allocator) void {
            inline for (std.meta.fields(Storage)) |field|
                @field(self.storage, field.name).deinit(alloc);
        }

        pub fn clear(self: *Self) void {
            inline for (std.meta.fields(Storage)) |field| {
                @field(self.storage, field.name).items.len = 0;
            }
        }

        pub fn pushAbsolute(
            self: *Self,
            alloc: std.mem.Allocator,
            value: T,
        ) std.mem.Allocator.Error!Index {
            switch (value) {
                inline else => |val, tag| {
                    if (comptime isInline(tag)) return Index.encodeStatic(tag, val).?;
                    const field = &@field(self.storage, @tagName(tag));
                    try field.append(alloc, val);
                    return .{ .tag = tag, .index = @intCast(field.items.len - 1) };
                },
            }
        }

        pub fn push(
            self: *Self,
            alloc: std.mem.Allocator,
            cp: Checkpoint,
            value: T,
        ) std.mem.Allocator.Error!Index {
            switch (value) {
                inline else => |val, tag| {
                    if (comptime isInline(tag)) return Index.encodeStatic(tag, val).?;
                    const field = &@field(self.storage, @tagName(tag));
                    const base = @field(cp, @tagName(tag));
                    try field.append(alloc, val);
                    return .{ .tag = tag, .index = @intCast(field.items.len - 1 - base) };
                },
            }
        }

        pub fn drainInto(self: *Self, other: *Self, source: Checkpoint, alloc: std.mem.Allocator) !Slice {
            var slice: Slice = undefined;
            inline for (std.meta.fields(Storage)) |field| {
                const src = &@field(self.storage, field.name);
                const src_slice = @field(source, field.name);
                const src_view = src.items[src_slice..];
                const dst = &@field(other.storage, field.name);
                const slc = &@field(slice, field.name);

                slc.index = @intCast(dst.items.len);
                slc.len = @intCast(src_view.len);
                try dst.appendSlice(alloc, src_view);
                src.items.len = src_slice;
            }
            return slice;
        }

        pub fn checkpoint(self: *const Self) Checkpoint {
            var cp: Checkpoint = undefined;
            inline for (std.meta.fields(Storage)) |field| {
                @field(cp, field.name) = @field(self.storage, field.name).items.len;
            }
            return cp;
        }

        pub fn view(self: *Self, slice: Slice) View {
            var vw: View = undefined;
            inline for (std.meta.fields(Storage)) |field| {
                const src = &@field(self.storage, field.name);
                const dst = @field(slice, field.name);
                @field(vw.view, field.name) = src.items[dst.index .. dst.index + dst.len];
            }
            return vw;
        }

        pub fn get(self: *Self, cp: Checkpoint, id: Index) AsPtr {
            switch (id.tag) {
                inline else => |tag| {
                    if (comptime isInline(tag)) return Index.decodeStatic(AsPtr, tag, id.index).?;
                    const field = &@field(self.storage, @tagName(tag));
                    const base = @field(cp, @tagName(tag));
                    return @unionInit(AsPtr, @tagName(tag), &field.items[base + id.index]);
                },
            }
        }

        pub fn getAbsolute(self: *const Self, id: Index) AsPtr {
            switch (id.tag) {
                inline else => |tag| {
                    if (comptime isInline(tag)) return Index.decodeStatic(AsPtr, tag, id.index).?;
                    const field = &@field(self.storage, @tagName(tag));
                    return @unionInit(AsPtr, @tagName(tag), &field.items[id.index]);
                },
            }
        }

        pub fn query(self: *const Self, comptime tag: std.meta.Tag(T)) []const std.meta.FieldType(T, tag) {
            return @field(self.storage, @tagName(tag)).items;
        }

        pub fn nextId(self: *const Self, comptime tag: std.meta.Tag(T)) Index {
            return .{ .tag = tag, .index = @intCast(self.query(tag).len) };
        }

        fn isInline(tag: std.meta.Tag(T)) bool {
            return !@hasField(Storage, @tagName(tag));
        }
    };
}

pub fn ShadowUnmanaged(comptime T: type, comptime ES: type) type {
    return struct {
        const Self = @This();
        const is_debug = @import("builtin").mode == .Debug;
        const BaseType = if (is_debug) ?T else T;
        const Storage = UnionStorage(ES.Item, lane);

        storage: Storage,

        fn lane(comptime _: type) type {
            return std.ArrayListUnmanaged(BaseType);
        }

        pub fn init(based_on: *const ES, alloc: std.mem.Allocator) !Self {
            var storage: Storage = undefined;
            inline for (std.meta.fields(Storage)) |nm| {
                if (nm.type == void) continue;
                @field(storage, nm.name) = .{};
                try @field(storage, nm.name).resize(alloc, @field(based_on.storage, nm.name).items.len);
                if (is_debug) {
                    for (@field(storage, nm.name).items) |*item| item.* = null;
                }
            }
            return .{ .storage = storage };
        }

        pub fn deinit(self: *Self, alloc: std.mem.Allocator) void {
            inline for (std.meta.fields(Storage)) |nm| {
                if (nm.type == void) continue;
                @field(self.storage, nm.name).deinit(alloc);
            }
        }

        pub fn at(self: *Self, id: ES.Index) ?*BaseType {
            return switch (id.tag) {
                inline else => |tag| {
                    if (!@hasField(Storage, @tagName(tag))) return null;
                    const field = &@field(self.storage, @tagName(tag));
                    return &field.items[id.index];
                },
            };
        }

        pub fn get(self: *const Self, id: ES.Index) ?T {
            return switch (id.tag) {
                inline else => |tag| {
                    const field = &@field(self.storage, @tagName(tag));
                    if (@TypeOf(field) == *const void) return null;
                    const value = field.items[id.index];
                    return if (is_debug) value.? else value;
                },
            };
        }
    };
}

test "sanity" {
    const Enum = union(enum) {
        A: u8,
        B: u16,
        C: u32,
        D,
        E,
        F: u32,
        G: u64,
        H: u64,
        I,
    };

    const Ctnr = Unmanaged(Enum);

    var ctnr = Ctnr.init();
    defer ctnr.deinit(std.testing.allocator);

    const cp = ctnr.checkpoint();

    const id = try ctnr.push(std.testing.allocator, cp, Enum.D);

    const val = ctnr.get(cp, id);
    try std.testing.expectEqual(val, Enum.D);

    const id2 = try ctnr.push(std.testing.allocator, cp, .{ .G = 1 });

    const val2 = ctnr.get(cp, id2);
    var a: u64 = 1;
    try std.testing.expectEqual(val2.G.*, a);

    const Shadow = ShadowUnmanaged(usize, Ctnr);

    var shadow = try Shadow.init(&ctnr, std.testing.allocator);
    defer shadow.deinit(std.testing.allocator);

    shadow.at(id2).?.* = 1;
    _ = ctnr.nextId(.G);

    var ctnr2 = Ctnr.init();
    defer ctnr2.deinit(std.testing.allocator);

    const slice = try ctnr.drainInto(&ctnr2, cp, std.testing.allocator);
    try std.testing.expectEqual(ctnr2.query(.G).len, 1);
    try std.testing.expectEqual(ctnr.query(.G).len, 0);

    const view = ctnr2.view(slice);

    try std.testing.expectEqual(view.get(id2).G, a);
    try std.testing.expectEqual(view.query(.G).len, 1);
}
