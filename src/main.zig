const std = @import("std");

const EnumList = @import("EnumList.zig");
const Ident = @import("Ident.zig");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const TypeCheck = @import("Typechk.zig");
const Codegen = @import("Codegen.zig");
const RegAlloc = @import("Codegen/RegAlloc.zig");
const Storage = @import("Storage.zig");

pub fn main() !void {
    // Prints to stderr (it's a shortcut based on `std.io.getStdErr()`)
    std.debug.print("All your {s} are belong to us.\n", .{"codebase"});

    // stdout is for the actual output of your application, for example if you
    // are implementing gzip, then only the compressed bytes should be sent to
    // stdout, not any debugging messages.
    const stdout_file = std.io.getStdOut().writer();
    var bw = std.io.bufferedWriter(stdout_file);
    const stdout = bw.writer();

    try stdout.print("Run `zig build test` to run the tests.\n", .{});

    try bw.flush(); // don't forget to flush!
}

test "simple test" {
    var list = std.ArrayList(i32).init(std.testing.allocator);
    defer list.deinit(); // try commenting this out and see if zig detects the memory leak!
    try list.append(42);
    try std.testing.expectEqual(@as(i32, 42), list.pop());
}
