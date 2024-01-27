const std = @import("std");
const Type = std.builtin.Type;

const BackingInt = u32;

pub fn isInlined(comptime Tag: type, comptime T: type) bool {
    return @bitSizeOf(T) < @bitSizeOf(BackingInt) - @bitSizeOf(Tag);
}

pub fn UnionAsPtr(comptime T: type) type {
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

pub fn Id(comptime T: type) type {
    const Index = @Type(.{ .Int = .{
        .signedness = std.builtin.Signedness.unsigned,
        .bits = @bitSizeOf(BackingInt) - @bitSizeOf(T),
    } });

    return packed struct(BackingInt) {
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

const EnumMetadata = struct {
    const Self = @This();

    index: type,
    union_types: []type,
    unions: []Type.Union,
    field_names: [][]const u8,
    omited_field_lookup: []?usize,

    pub fn construct(comptime T: type) Self {
        const meta = @typeInfo(T).Union;
        const Tag = meta.tag_type.?;

        comptime var distinct_layout_count = meta.fields.len;
        comptime var omited_field_lookup: [meta.fields.len]?usize = undefined;
        for (meta.fields, 0..) |field, i| {
            if (isInlined(Tag, field.type)) {
                distinct_layout_count -= 1;
                continue;
            }

            for (i + 1..meta.fields.len) |j| {
                if (@alignOf(field.type) == @alignOf(meta.fields[j].type) and
                    @sizeOf(field.type) == @sizeOf(meta.fields[j].type))
                {
                    distinct_layout_count -= 1;
                    break;
                }
            }
        }

        comptime var unions: [distinct_layout_count]Type.Union = undefined;
        comptime var field_names: [distinct_layout_count][]const u8 = undefined;
        comptime var size_and_align: [distinct_layout_count]struct { usize, usize } = undefined;
        comptime var union_index = 0;

        o: for (meta.fields, 0..) |field, i| {
            if (isInlined(Tag, field.type)) {
                omited_field_lookup[i] = null;
                continue;
            }

            for (unions[0..union_index], size_and_align[0..union_index], 0..) |*un, sa, j| {
                if (sa[0] == @alignOf(field.type) and sa[1] == @sizeOf(field.type)) {
                    omited_field_lookup[i] = j;

                    for (un.fields) |f| {
                        if (f.type == field.type) {
                            continue :o;
                        }
                    }

                    const newField: Type.UnionField = .{
                        .name = field.name,
                        .type = field.type,
                        .alignment = @alignOf(field.type),
                    };
                    un.fields = un.fields ++ .{newField};

                    continue :o;
                }
            }

            omited_field_lookup[i] = union_index;
            unions[union_index] = .{
                .tag_type = null,
                .fields = &.{.{ .name = field.name, .type = field.type, .alignment = @alignOf(field.type) }},
                .layout = Type.ContainerLayout.Auto,
                .decls = &[0]Type.Declaration{},
            };

            field_names[union_index] = field.name;
            size_and_align[union_index] = .{ @alignOf(field.type), @sizeOf(field.type) };
            union_index += 1;
        }

        comptime var union_types: [distinct_layout_count]type = undefined;
        for (unions, &union_types) |un, *ty| {
            ty.* = @Type(.{ .Union = un });
        }

        return .{
            .index = Id(meta.tag_type.?),
            .unions = &unions,
            .field_names = &field_names,
            .union_types = &union_types,
            .omited_field_lookup = &omited_field_lookup,
        };
    }

    pub fn createStorage(comptime self: Self) type {
        var storage: [self.unions.len]Type.StructField = undefined;
        for (self.field_names, self.union_types, 0..) |nm, un, i| {
            const ty = std.ArrayListUnmanaged(un);
            storage[i] = .{
                .name = nm,
                .type = ty,
                .alignment = @alignOf(ty),
                .default_value = null,
                .is_comptime = false,
            };
        }

        return @Type(.{ .Struct = .{
            .fields = &storage,
            .layout = Type.ContainerLayout.Auto,
            .decls = &.{},
            .backing_integer = null,
            .is_tuple = false,
        } });
    }
};

pub fn Unmanaged(comptime T: type) type {
    return struct {
        const Self = @This();

        pub const meta = EnumMetadata.construct(T);
        pub const Storage = meta.createStorage();
        const Index = meta.index;
        pub const AsPtr = UnionAsPtr(T);

        storage: Storage,

        pub fn init() Self {
            var storage: Storage = undefined;
            inline for (meta.field_names) |nm| @field(storage, nm) = .{};
            return .{ .storage = storage };
        }

        pub fn deinit(self: *Self, alloc: std.mem.Allocator) void {
            inline for (meta.field_names) |nm| @field(self.storage, nm).deinit(alloc);
        }

        pub fn clear(self: *Self) void {
            inline for (meta.field_names) |nm| @field(self.storage, nm).items.len = 0;
        }

        pub fn push(self: *Self, alloc: std.mem.Allocator, value: T) std.mem.Allocator.Error!Index {
            switch (value) {
                inline else => |val, tag| {
                    if (Index.encodeStatic(tag, val)) |id| return id;

                    inline for (meta.field_names, meta.unions, meta.union_types) |nm, un, un_ty| {
                        inline for (un.fields) |f| {
                            if (f.type == @TypeOf(val)) {
                                var v = @unionInit(un_ty, f.name, val);
                                try @field(self.storage, nm).append(alloc, v);
                                return .{ .tag = tag, .index = @intCast(@field(self.storage, nm).items.len - 1) };
                            }
                        }
                    }
                },
            }

            unreachable;
        }

        pub fn find_or_push(self: *Self, alloc: std.mem.Allocator, value: T) std.mem.Allocator.Error!Index {
            switch (value) {
                inline else => |val, tag| {
                    if (Index.encodeStatic(tag, val)) |id| return id;

                    inline for (meta.field_names, meta.unions, meta.union_types) |nm, un, un_ty| {
                        inline for (un.fields) |f| {
                            if (f.type != @TypeOf(val)) continue;
                            for (@field(self.storage, nm).items, 0..) |item, i| {
                                if (std.meta.eql(val, @field(item, f.name))) return .{ .tag = tag, .index = @intCast(i) };
                            }
                            var v = @unionInit(un_ty, f.name, val);
                            try @field(self.storage, nm).append(alloc, v);
                            return .{ .tag = tag, .index = @intCast(@field(self.storage, nm).items.len - 1) };
                        }
                    }
                },
            }

            unreachable;
        }

        pub fn get(self: *const Self, id: Index) T {
            switch (id.tag) {
                inline else => |tag| {
                    if (Index.decodeStatic(T, tag, id.index)) |val| return val;

                    const field = @typeInfo(T).Union.fields[@intFromEnum(tag)];
                    inline for (meta.field_names, meta.unions) |nm, un| {
                        inline for (un.fields) |f| {
                            if (f.type == field.type) {
                                return @unionInit(T, f.name, @field(@field(self.storage, nm).items[id.index], f.name));
                            }
                        }
                    }
                },
            }

            unreachable;
        }

        pub fn get_ptr(self: *Self, id: Index) AsPtr {
            switch (id.tag) {
                inline else => |tag| {
                    if (Index.decodeStatic(AsPtr, tag, id.index)) |val| return val;

                    const field = @typeInfo(T).Union.fields[@intFromEnum(tag)];

                    inline for (meta.field_names, meta.unions) |nm, un| {
                        inline for (un.fields) |f| {
                            if (f.type == field.type) {
                                return @unionInit(AsPtr, f.name, &@field(@field(self.storage, nm).items[id.index], f.name));
                            }
                        }
                    }
                },
            }

            unreachable;
        }
    };
}

pub fn ShadowUnmanaged(comptime T: type, comptime ES: type) type {
    return struct {
        const Self = @This();
        const meta: EnumMetadata = ES.meta;

        const Lane = std.ArrayListUnmanaged(T);
        const Storage = b: {
            var fields: [meta.field_names.len]Type.StructField = undefined;
            for (meta.field_names, &fields) |nm, *f| {
                f.* = .{
                    .name = nm,
                    .type = Lane,
                    .alignment = @alignOf(Lane),
                    .default_value = null,
                    .is_comptime = false,
                };
            }

            break :b @Type(.{ .Struct = .{
                .fields = &fields,
                .layout = Type.ContainerLayout.Auto,
                .decls = &.{},
                .backing_integer = null,
                .is_tuple = false,
            } });
        };

        storage: Storage,

        pub fn init(based_on: *const ES, alloc: std.mem.Allocator) !Self {
            var storage: Storage = undefined;
            inline for (meta.field_names) |nm| {
                @field(storage, nm) = .{};
                try @field(storage, nm).resize(alloc, @field(based_on.storage, nm).items.len);
            }
            return .{ .storage = storage };
        }

        pub fn deinit(self: *Self, alloc: std.mem.Allocator) void {
            inline for (meta.field_names) |nm| @field(self.storage, nm).deinit(alloc);
        }

        pub fn at(self: *Self, id: meta.index) ?*T {
            return switch (id.tag) {
                inline else => |tag| self.dispatch(@intFromEnum(tag), id.index),
            };
        }

        pub fn get(self: *const Self, id: meta.index) ?T {
            return switch (id.tag) {
                inline else => |tag| self.dispatch_get(@intFromEnum(tag), id.index),
            };
        }

        fn dispatch_get(self: *const Self, comptime tag: usize, index: usize) ?T {
            const i = meta.omited_field_lookup[tag] orelse return null;
            return @field(self.storage, meta.field_names[i]).items[index];
        }

        fn dispatch(self: *Self, comptime tag: usize, index: usize) ?*T {
            const i = meta.omited_field_lookup[tag] orelse return null;
            return &@field(self.storage, meta.field_names[i]).items[index];
        }
    };
}

test "sanity" {
    std.testing.refAllDeclsRecursive(EnumMetadata);

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

    const id = try ctnr.push(
        std.testing.allocator,
        Enum.D,
    );

    const val = ctnr.get(id);
    try std.testing.expectEqual(val, Enum.D);

    const id2 = try ctnr.push(
        std.testing.allocator,
        .{ .G = 1 },
    );

    const val2 = ctnr.get_ptr(id2);
    var a: u64 = 1;
    try std.testing.expectEqual(val2.G.*, a);

    const Shadow = ShadowUnmanaged(usize, Ctnr);

    var shadow = try Shadow.init(&ctnr, std.testing.allocator);
    defer shadow.deinit(std.testing.allocator);

    shadow.at(id2).?.* = 1;
}
