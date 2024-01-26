const std = @import("std");

const Self = @This();

const Storage = std.PackedIntArray(u6, cap);
pub const Store = struct {
    const Item = union {
        val: Storage,
        index: usize,
    };

    allocator: std.mem.Allocator,
    pool: std.SegmentedList(Item, 0),
    free_head: ?usize,

    pub fn init(allocator: std.mem.Allocator) Store {
        return .{
            .allocator = allocator,
            .pool = .{},
            .free_head = null,
        };
    }

    pub fn deinit(self: *Store) void {
        self.pool.deinit(self.allocator);
    }

    pub fn create(self: *Store) std.mem.Allocator.Error!*Storage {
        const ptr = if (self.free_head) |head| b: {
            if (self.pool.uncheckedAt(head).index != head) {
                self.free_head = self.pool.uncheckedAt(head).index;
            } else {
                self.free_head = null;
            }

            break :b self.pool.uncheckedAt(head);
        } else b: {
            break :b try self.pool.addOne(self.allocator);
        };

        ptr.* = .{ .val = .{ .bytes = [_]u8{0} ** (cap * 6 / 8) } };
        return &ptr.val;
    }

    pub fn destroy(self: *Store, storage: *Storage) void {
        for (0..self.pool.dynamic_segments.len) |ri| {
            const i = self.pool.dynamic_segments.len - 1 - ri;
            const segment = self.pool.dynamic_segments[i];
            if (@intFromPtr(segment) > @intFromPtr(storage) or
                @intFromPtr(segment) + (@as(usize, 1) << @intCast(i)) < @intFromPtr(storage)) continue;

            const index = (@intFromPtr(storage) - @intFromPtr(segment)) / @sizeOf(Storage) + (@as(usize, 1) << @as(u6, @intCast(i))) - 1;
            self.pool.uncheckedAt(index).* = .{ .index = self.free_head orelse index };
            self.free_head = index;
        }
    }
};

pub const cap: usize = 64;
const sentinel: u6 = 0;
const maxAsciiValue: usize = 127;
const encodeTable: [maxAsciiValue]u6 = b: {
    comptime var arr = [_]u6{0} ** maxAsciiValue;
    comptime var cursor: u6 = 1;

    for ('0'..'9' + 1) |c| {
        arr[c] = cursor;
        cursor += 1;
    }

    for ('A'..'Z' + 1) |c| {
        arr[c] = cursor;
        cursor += 1;
    }

    arr['_'] = cursor;
    cursor += 1;

    for ('a'..'z' + 1) |c| {
        arr[c] = cursor;
        cursor = @addWithOverflow(cursor, 1)[0];
    }

    std.debug.assert(cursor == 0);

    break :b arr;
};

const decodeTable: [cap]u8 = b: {
    comptime var arr = [_]u8{0} ** cap;
    comptime var cursor: u8 = 1;

    for ('0'..'9' + 1) |c| {
        arr[cursor] = c;
        cursor += 1;
    }

    for ('A'..'Z' + 1) |c| {
        arr[cursor] = c;
        cursor += 1;
    }

    arr[cursor] = '_';
    cursor += 1;

    for ('a'..'z' + 1) |c| {
        arr[cursor] = c;
        cursor += 1;
    }

    std.debug.assert(cursor == 64);

    break :b arr;
};

str: *Storage,

pub fn init(alloc: *Store) !Self {
    return Self{ .str = try alloc.create() };
}

pub fn deinit(self: *const Self, alloc: *Store) void {
    alloc.destroy(self.str);
}

pub fn set(self: *Self, value: []const u8) void {
    for (value, 0..@min(cap, value.len)) |c, i| {
        self.str.set(i, encodeTable[c]);
    }
}

pub fn get(self: Self, buf: *[cap]u8) []const u8 {
    for (0..cap) |i| {
        const c = self.str.get(i);
        if (c == sentinel) {
            return buf[0..i];
        }
        buf[i] = decodeTable[c];
    }
    return buf;
}

pub fn equalSymbol(self: Self, other: Self) bool {
    return @intFromPtr(self.str) == @intFromPtr(other.str);
}

pub fn equalContent(self: Self, other: Self) bool {
    // reminder elements are always 0
    return std.mem.eql(u8, &self.str.bytes, &other.str.bytes);
}

test {
    std.testing.refAllDecls(Self);
}

test "encode decode" {
    var st = Store.init(std.testing.allocator);
    defer st.deinit();

    var s = try Self.init(&st);
    defer s.deinit(&st);

    s.set("hello");

    var buf = [_]u8{0} ** cap;
    var result = s.get(&buf);

    try std.testing.expectEqualStrings(result, "hello");
}

test "init deinit many" {
    var st = Store.init(std.testing.allocator);
    defer st.deinit();

    const counts = [_]usize{ 1, 1, 3, 2, 4, 5, 3, 3 };
    var allocated = std.ArrayList(Self).init(std.testing.allocator);
    defer allocated.deinit();

    var idx: usize = 0;
    while (idx < counts.len) : (idx += 2) {
        for (0..counts[idx]) |_| {
            var s = try Self.init(&st);
            try allocated.append(s);
        }

        for (0..counts[idx + 1]) |_| {
            allocated.pop().deinit(&st);
        }
    }
}
