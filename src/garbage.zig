const std = @import("std");

pub const CountingAllocator = struct {
    child_allocator: std.mem.Allocator,
    count_active: u64,
    count_total: u64,
    count_allocs: u64,
    count_allocs_success: u64,
    count_resizes: u64,
    count_frees: u64,

    const extras = struct {
        pub fn ptrCast(comptime T: type, ptr: *anyopaque) *T {
            return @as(*T, @ptrCast(@alignCast(ptr)));
        }
    };

    pub fn print(self: *CountingAllocator) void {
        std.log.info("active: {d} total: {d} allocs: {d} success: {d} resizes: {d} frees: {d}", .{
            self.count_active,
            self.count_total,
            self.count_allocs,
            self.count_allocs_success,
            self.count_resizes,
            self.count_frees,
        });
    }

    pub fn init(child_allocator: std.mem.Allocator) CountingAllocator {
        return .{
            .child_allocator = child_allocator,
            .count_active = 0,
            .count_total = 0,
            .count_allocs = 0,
            .count_allocs_success = 0,
            .count_resizes = 0,
            .count_frees = 0,
        };
    }

    pub fn allocator(self: *CountingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .free = free,
            },
        };
    }

    fn alloc(ctx: *anyopaque, len: usize, ptr_align: u8, ret_addr: usize) ?[*]u8 {
        var self = extras.ptrCast(CountingAllocator, ctx);
        self.count_allocs += 1;
        const ptr = self.child_allocator.rawAlloc(len, ptr_align, ret_addr) orelse return null;
        self.count_allocs_success += 1;
        self.count_active += len;
        self.count_total += len;
        return ptr;
    }

    fn resize(ctx: *anyopaque, buf: []u8, buf_align: u8, new_len: usize, ret_addr: usize) bool {
        var self = extras.ptrCast(CountingAllocator, ctx);
        self.count_resizes += 1;
        const old_len = buf.len;
        const stable = self.child_allocator.rawResize(buf, buf_align, new_len, ret_addr);
        if (stable) {
            if (new_len > old_len) {
                self.count_active += new_len;
                self.count_active -= old_len;
                self.count_total += new_len;
                self.count_total -= old_len;
            } else {
                self.count_active -= old_len;
                self.count_active += new_len;
                self.count_total -= old_len;
                self.count_total += new_len;
            }
        }
        return stable;
    }

    fn free(ctx: *anyopaque, buf: []u8, buf_align: u8, ret_addr: usize) void {
        var self = extras.ptrCast(CountingAllocator, ctx);
        self.count_frees += 1;
        self.count_active -= buf.len;
        return self.child_allocator.rawFree(buf, buf_align, ret_addr);
    }
};

pub fn printtest(comptime name: []const u8, comptime tst: anytype, ctx: anytype) !void {
    try runPrinttest(name, tst, ctx);
}

fn runPrinttest(comptime name: []const u8, comptime tst: anytype, ctx: anytype) !void {
    const out_folder = "test_output";

    try std.fs.cwd().makePath(out_folder);
    const out_path = out_folder ++ "/" ++ name;
    const out_file = std.fs.cwd().openFile(out_path, .{ .mode = .read_write }) catch
        try std.fs.cwd().createFile(out_path, .{});
    defer out_file.close();

    const end = try out_file.getEndPos();
    const bytes = try std.heap.page_allocator.alloc(u8, end);
    defer std.heap.page_allocator.free(bytes);
    const red = try out_file.readAll(bytes);
    std.debug.assert(red == bytes.len);

    var buffer = std.ArrayList(u8).init(std.heap.page_allocator);
    defer buffer.deinit();
    var writer = buffer.writer();
    var alloc = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = alloc.deinit();

    const err = tst(writer, name, alloc.allocator(), ctx);

    if (std.mem.eql(u8, bytes, buffer.items)) return;

    if (bytes.len == 0) {
        try out_file.writeAll(buffer.items);
        std.log.warn("new test detected: {s}", .{name});
        std.log.warn("test output:\n{s}", .{buffer.items});
        return;
    }

    if (std.os.getenv("UPDATE_TESTS") != null) {
        try out_file.seekTo(0);
        try out_file.setEndPos(0);
        try out_file.writeAll(buffer.items);
        return;
    }

    const draft_path = out_path ++ ".draft";
    const draft_file = try std.fs.cwd().createFile(draft_path, .{});
    defer draft_file.close();

    try draft_file.writeAll(buffer.items);

    var child = std.process.Child.init(
        &.{ "/usr/bin/diff", "--color", "-y", "--left-column", out_path, draft_path },
        std.heap.page_allocator,
    );
    _ = try child.spawnAndWait();

    try err;
    return error.DiffFailed;
}

pub fn toLowerCt(comptime str: []const u8) []const u8 {
    comptime var buffer: [str.len]u8 = undefined;
    inline for (&buffer, str) |*b, c| b.* = comptime std.ascii.toLower(c);
    return &buffer;
}
