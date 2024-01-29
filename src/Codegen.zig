//const std = @import("std");
//const Parser = @import("Parser.zig");
//const Ast = Parser.Ast;
//const Typechk = @import("Typechk.zig");
//const Types = Typechk.Module;
//const Type = Typechk.Type;
//const EnumList = @import("EnumList.zig");
//
//const arg_regs = [_]Reg{ .rdi, .rsi, .rdx, .rcx, .r8, .r9 };
//const prealloc_count = 4;
//
//const Self = @This();
//
//const Reg = enum {
//    rax,
//    rbx,
//    rcx,
//    rdx,
//    rsi,
//    rdi,
//    rbp,
//    rsp,
//    r8,
//    r9,
//    r10,
//    r11,
//    r12,
//    r13,
//    r14,
//    r15,
//};
//
//// For Nasm
//const File = struct {
//    const Label = u32;
//
//    const Func = struct {
//        label: Label,
//        stack_size: u32 = 0,
//    };
//
//    text: std.ArrayList(u8),
//
//    pub fn init(alloc: std.mem.Allocator) File {
//        return .{
//            .text = std.ArrayList(u8).init(alloc),
//        };
//    }
//
//    pub fn deinit(self: *File) void {
//        self.text.deinit();
//    }
//
//    // returns offset to which stack size should be written
//    pub fn writeStackSetup(self: *File) !usize {
//        var wrt = self.text.writer();
//        try wrt.writeAll(
//            \\    push rbp
//            \\    mov rbp, rsp
//            \\    sub rsp, 0x
//        );
//        const offset = self.text.items.len;
//        try wrt.writeAll("      \n");
//        return offset;
//    }
//
//    pub fn writeStackFrameSize(self: *File, offset: usize, size: u32) !void {
//        var st = std.io.fixedBufferStream(self.text.items[offset..][0..6]);
//        var wrt = st.writer();
//        wrt.print("{x}", .{size}) catch return error.OutOfMemory;
//    }
//
//    pub fn writeLabel(self: *File, label: File.Label) !void {
//        var wrt = self.text.writer();
//        if (label != 0)
//            try wrt.print("L{x}:\n", .{label})
//        else
//            try wrt.writeAll("main:\n");
//    }
//
//    pub fn writeInstr(self: *File, instr: []const u8, args: []const Loc) !void {
//        if (std.mem.eql(u8, instr, "mov") and std.meta.eql(args[0], args[1])) return;
//
//        var wrt = self.text.writer();
//        try wrt.writeAll("    ");
//        try wrt.print("{s} ", .{instr});
//        for (args, 0..) |arg, i| {
//            switch (arg) {
//                .Reg => |reg| try wrt.print("{s}", .{@tagName(reg)}),
//                .Imm => |imm| try wrt.print("{d}", .{imm}),
//                .Stack => |stack| try wrt.print("{d}(rbp)", .{stack.offset}),
//                .Label => |label| if (label != 0) try wrt.print("L{x}", .{label}) else try wrt.writeAll("main"),
//                .Comptime => unreachable,
//            }
//            if (i + 1 != args.len) try wrt.writeAll(", ");
//        }
//        try wrt.writeByte('\n');
//    }
//
//    pub fn print(self: *File, writer: anytype) !void {
//        try writer.writeAll(
//            \\    global main
//            \\
//            \\    section .text
//            \\
//        );
//        try writer.writeAll(self.text.items);
//    }
//};
//
//pub const Stack = struct {
//    offset: u32, // from frame base
//};
//
//const Loc = union(enum) {
//    Reg: Reg,
//    Imm: u64,
//    Stack: Stack,
//    Label: File.Label,
//    Comptime,
//};
//
//pub const Value = union(enum) {
//    Owned: Loc,
//    Borrowed: usize,
//    None,
//};
//
//const Error = error{} || std.mem.Allocator.Error;
//
//const InnerError = error{Returned} || Error;
//
//label_count: File.Label,
//funcs: []File.Func,
//ast: *const Ast,
//types: *const Types,
//file: *File,
//scope: *Scope,
//source: []const u8,
//
//pub fn generate(alloc: std.mem.Allocator, ast: *const Ast, types: *const Types, source: []const u8) Error!File {
//    var file = File.init(alloc);
//
//    var scope = try Scope.init(alloc, types.max_stack);
//    defer scope.deinit(alloc);
//
//    const funcs = try alloc.alloc(File.Func, ast.items.items.len);
//    defer alloc.free(funcs);
//    for (types.reached_functions, 0..) |func, i|
//        funcs[func.index] = .{ .label = @intCast(i) };
//
//    var self = Self{
//        .label_count = @intCast(funcs.len),
//        .funcs = funcs,
//        .ast = ast,
//        .types = types,
//        .file = &file,
//        .scope = &scope,
//        .source = source,
//    };
//
//    try self.gen();
//
//    return file;
//}
//
//fn gen(self: *Self) Error!void {
//    for (self.ast.items.items) |item| {
//        switch (self.ast.item_store.get(item)) {
//            .Func => |f| try self.genFunc(f, item.index),
//        }
//    }
//}
//
//fn genFunc(self: *Self, func: Ast.Item.Func, label: File.Label) Error!void {
//    const ret = self.types.getValue(func.ret).data.type;
//
//    self.scope.clear(ret);
//
//    if (!ret.eql(Type.usize_lit)) @panic("TODO: function return type");
//    //if (func.params.len > 0) @panic("TODO: function parameters");
//    for (func.params, arg_regs[0..func.params.len], 0..) |param, reg, i| {
//        const value = self.types.getValue(param.type);
//        self.scope.slots[i] = .{ .type = value.data.type, .loc = .{ .Reg = reg } };
//    }
//
//    try self.file.writeLabel(label);
//    const size_offset = try self.file.writeStackSetup();
//    _ = self.genBlock(func.body) catch |err| switch (err) {
//        error.Returned => {},
//        else => |e| return e,
//    };
//    try self.file.writeStackFrameSize(size_offset, self.funcs[label].stack_size);
//}
//
//fn genBlock(self: *Self, block: Ast.Expr.Block) InnerError!Value {
//    const frame = self.scope.pushFrame();
//    for (block) |expr| {
//        _ = try self.genExpr(expr);
//    }
//    self.scope.popFrame(frame);
//    return .None;
//}
//
//fn genExpr(self: *Self, expr: Ast.Expr.Id) InnerError!Value {
//    const value = self.types.getValue(expr);
//    if (!value.is_runtime and expr.tag != .Ret) {
//        return self.createValue(value);
//    }
//
//    return switch (self.ast.expr_store.get(expr)) {
//        .Var => |v| try self.genVar(v, value),
//        .Ret => |r| try self.genRet(r),
//        .Binary => |b| try self.genBinary(b),
//        .Ident => |i| try self.genIdent(i, value),
//        .Int => |i| .{ .Owned = .{ .Imm = i } },
//        .Call => |c| try self.genCall(c, value),
//        inline else => |v, t| std.debug.panic("TODO: {any} {any}", .{ t, v }),
//    };
//}
//
//fn genCall(self: *Self, c: Ast.Expr.Call, value: Typechk.Value) InnerError!Value {
//    _ = value;
//    try self.prepareCall(c.args);
//
//    const func = self.types.getValue(c.callee).data.decl;
//    const label = self.funcs[func.index].label;
//    try self.file.writeInstr("call", &.{.{ .Label = label }});
//
//    self.cleanupCall(c.args);
//
//    const reg = self.scope.regs.alloc() orelse @panic("todo");
//    try self.file.writeInstr("mov", &.{ .{ .Reg = reg }, .{ .Reg = .rax } });
//
//    return .{ .Owned = .{ .Reg = reg } };
//}
//
//fn genBinary(self: *Self, b: Ast.Expr.Binary) InnerError!Value {
//    return switch (b.op) {
//        .Add, .Sub => try self.genMathOp(b),
//        .Assign => try self.genAssign(b),
//    };
//}
//
//fn genMathOp(self: *Self, b: Ast.Expr.Binary) InnerError!Value {
//    const lhs = try self.genExpr(b.lhs);
//    const rhs = try self.genExpr(b.rhs);
//
//    var instr = switch (b.op) {
//        .Add => "add",
//        .Sub => "sub",
//        else => unreachable,
//    };
//
//    var mutability = [_]bool{ self.isMutable(lhs), self.isMutable(rhs) };
//    var args = [_]Loc{ self.loadValue(lhs), self.loadValue(rhs) };
//    var arg_count: usize = 2;
//
//    if (args[0] == .Imm) {
//        if (args[0].Imm == 1) {
//            instr = switch (b.op) {
//                .Add => "inc",
//                .Sub => "dec",
//                else => unreachable,
//            };
//            arg_count = 1;
//        }
//
//        if (b.op == .Sub) args[0].Imm = ~args[0].Imm - 1;
//        std.mem.reverse(Loc, &args);
//        std.mem.reverse(bool, &mutability);
//    }
//
//    if (!mutability[0] and mutability[1] and arg_count == 2 and b.op == .Add) {
//        std.mem.reverse(Loc, &args);
//        std.mem.reverse(bool, &mutability);
//    }
//
//    if (!mutability[0]) {
//        const reg = self.scope.regs.alloc() orelse @panic("todo");
//        try self.file.writeInstr("mov", &.{ .{ .Reg = reg }, args[0] });
//        args[0] = .{ .Reg = reg };
//    }
//
//    try self.file.writeInstr(instr, args[0..arg_count]);
//
//    if (arg_count == 2 and args[1] == .Reg) {
//        self.scope.regs.free(args[1].Reg);
//    }
//
//    return .{ .Owned = args[0] };
//}
//
//fn genAssign(self: *Self, binary: Ast.Expr.Binary) InnerError!Value {
//    const target = try self.genExpr(binary.lhs);
//    const value = try self.genExpr(binary.rhs);
//
//    const target_loc = self.loadValue(target);
//    const value_loc = self.loadValue(value);
//
//    try self.file.writeInstr("mov", &.{ target_loc, value_loc });
//
//    return .None;
//}
//
//fn genIdent(_: *Self, _: Ast.Ident, value: Typechk.Value) InnerError!Value {
//    if (!value.is_runtime) return .{ .Owned = .{ .Imm = value.data.int } };
//    return .{ .Borrowed = value.data.index };
//}
//
//fn genVar(self: *Self, variable: Ast.Expr.Var, value: Typechk.Value) InnerError!Value {
//    const rt_value = try self.genExpr(variable.init);
//    const to_store = try self.ensureMutable(rt_value);
//    self.scope.slots[value.data.index - self.funcs.len] = .{ .type = value.type, .loc = to_store };
//    return .None;
//}
//
//fn genRet(self: *Self, ret: Ast.Expr.Id) InnerError!Value {
//    const value = try self.genExpr(ret);
//    try self.file.writeInstr("mov", &.{ .{ .Reg = .rax }, self.loadValue(value) });
//    try self.file.text.appendSlice(
//        \\    mov rsp, rbp
//        \\    pop rbp
//        \\    ret
//        \\
//    );
//    return InnerError.Returned;
//}
//
//fn isMutable(_: *Self, value: Value) bool {
//    return switch (value) {
//        .Owned => |v| v != .Imm,
//        .Borrowed => false,
//        .None => unreachable,
//    };
//}
//
//fn prepareCall(self: *Self, args: []const Ast.Expr.Id) InnerError!void {
//    if (args.len > arg_regs.len) @panic("TODO: function calls with more than 6 arguments");
//
//    const common_prealloc_count = @min(args.len, prealloc_count);
//    for (args[0..common_prealloc_count], arg_regs[0..common_prealloc_count]) |arg, reg| {
//        const value = try self.genExpr(arg);
//        const loc = self.loadValue(value);
//        try self.file.writeInstr("mov", &.{ .{ .Reg = reg }, loc });
//    }
//
//    if (args.len == common_prealloc_count) return;
//
//    const common_extra_len = @min(args.len, arg_regs.len);
//    for (args[prealloc_count..common_extra_len], arg_regs[prealloc_count..common_extra_len]) |arg, reg| {
//        const value = try self.genExpr(arg);
//        const loc = self.loadValue(value);
//        if (loc == .Reg and loc.Reg == reg) continue;
//        self.scope.regs.allocSpecific(reg) catch @panic("TODO: ups");
//    }
//}
//
//fn cleanupCall(self: *Self, args: []const Ast.Expr.Id) void {
//    if (args.len > arg_regs.len) @panic("TODO: function calls with more than 6 arguments");
//    if (args.len <= prealloc_count) return;
//
//    const common_extra_len = @min(args.len, arg_regs.len);
//    for (arg_regs[prealloc_count..common_extra_len]) |reg| self.scope.regs.free(reg);
//}
//
//fn ensureMutable(self: *Self, value: Value) InnerError!Loc {
//    const should_copy = value == .Borrowed;
//    const loc = self.loadValue(value);
//    switch (loc) {
//        .Imm => |i| {
//            const reg = self.scope.regs.alloc() orelse @panic("todo");
//            const new_loc = .{ .Reg = reg };
//            if (i == 0) {
//                try self.file.writeInstr("xor", &.{ new_loc, new_loc });
//            } else {
//                try self.file.writeInstr("mov", &.{ new_loc, .{ .Imm = i } });
//            }
//            return new_loc;
//        },
//        .Reg => if (should_copy) {
//            const reg = self.scope.regs.alloc() orelse @panic("todo");
//            const new_loc = .{ .Reg = reg };
//            try self.file.writeInstr("mov", &.{ new_loc, loc });
//            return new_loc;
//        },
//        inline else => |v, t| std.debug.panic("TODO: {any} {any}", .{ v, t }),
//    }
//
//    return loc;
//}
//
//fn loadValue(self: *Self, value: Value) Loc {
//    return switch (value) {
//        .Owned => |v| v,
//        .Borrowed => |v| self.scope.slots[v - self.funcs.len].loc,
//        .None => unreachable,
//    };
//}
//
//fn createValue(self: *Self, value: Typechk.Value) Value {
//    std.debug.assert(!value.is_runtime);
//    return switch (self.types.store.get(value.type)) {
//        .Int => |i| {
//            if (i.bit_width != 64) std.debug.panic("TODO: {any}", .{i});
//            return .{ .Owned = .{ .Imm = value.data.int } };
//        },
//        .Void => return .None,
//        .Type, .Decl => unreachable,
//    };
//}
//
//fn allocLabel(self: *Self) File.Label {
//    defer self.label_count += 1;
//    return self.label_count;
//}
//
//test "sanity" {
//    const alloc = std.testing.allocator;
//    const src =
//        \\fn main() usize {
//        \\    const i = 1 + 2;
//        \\    const j = i + 3;
//        \\    var k: usize = j;
//        \\    k = k + 5 + foo(4);
//        \\    return k;
//        \\}
//        \\
//        \\fn foo(a: usize) usize {
//        \\    return a + a + 4;
//        \\}
//    ;
//
//    var ast = try Parser.parse(alloc, src);
//    defer ast.deinit(alloc);
//    for (ast.errors.items) |err| std.log.warn("{any}", .{err});
//    try std.testing.expect(ast.errors.items.len == 0);
//    try std.testing.expect(ast.items.items.len == 2);
//
//    // var buffer = [1]u8{0} ** 10000;
//    // var st = std.io.fixedBufferStream(&buffer);
//    // var wr = st.writer();
//    // var printer = Parser.Printer(@TypeOf(wr)).init(&ast, wr, src);
//    // try printer.print();
//
//    // std.log.warn("{s}", .{buffer});
//
//    var types = try Typechk.check(alloc, &ast, src);
//    defer types.deinit(alloc);
//
//    var file = try generate(alloc, &ast, &types, src);
//    defer file.deinit();
//
//    const file_name = "test.asm";
//    const obj_name = "test.o";
//    var local_file = try std.fs.cwd().createFile(file_name, .{});
//    defer local_file.close();
//    var writer = local_file.writer();
//    try file.print(writer);
//
//    try run(alloc, &.{ "/usr/bin/nasm", file_name, "-felf64", "-o", obj_name }, 0);
//    try run(alloc, &.{ "/usr/bin/gcc", "-o", "test", obj_name }, 0);
//    try run(alloc, &.{"./test"}, 23);
//}
//
//fn run(alloc: std.mem.Allocator, args: []const []const u8, expected: u8) !void {
//    var child = std.ChildProcess.init(args, alloc);
//    const res = try child.spawnAndWait();
//    try std.testing.expect(res.Exited == expected);
//}
