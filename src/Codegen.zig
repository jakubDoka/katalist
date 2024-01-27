const std = @import("std");
const Parser = @import("Parser.zig");
const Ast = Parser.Ast;
const Typechk = @import("Typechk.zig");
const Types = Typechk.Module;
const Type = Typechk.Type;
const EnumList = @import("EnumList.zig");

const Self = @This();

const Reg = enum {
    rax,
    rbx,
    rcx,
    rdx,
    rsi,
    rdi,
    rbp,
    rsp,
    r8,
    r9,
    r10,
    r11,
    r12,
    r13,
    r14,
    r15,
};

const RegAlloc = struct {
    const reg_count = std.meta.fields(Reg).len;
    const AllocMask = std.meta.Int(.unsigned, reg_count);

    regs: AllocMask = 0,
    used: AllocMask = 0,
    spills: [reg_count]u16 = [_]u16{0} ** reg_count,

    pub fn alloc(self: *RegAlloc) ?Reg {
        // we allocate beckwards so that instruction specific registers are allocated as last resort
        const pos = @ctz(~self.regs);
        if (pos == reg_count) return null;
        self.regs |= @as(AllocMask, 1) << pos;
        self.used |= @as(AllocMask, 1) << pos;
        return @enumFromInt(pos);
    }

    pub fn free(self: *RegAlloc, reg: Reg) void {
        self.regs &= ~(@as(AllocMask, 1) << @intFromEnum(reg));
    }

    pub fn spill(self: *RegAlloc, reg: Reg) void {
        const pos = @intFromEnum(reg);
        self.spills[pos] += 1;
    }
};

const File = struct {
    const Label = u32;

    const Arg = union(enum) {
        Reg: Reg,
        Imm: u64,
        Label: Label,
    };

    const Func = struct {
        label: Label,
    };

    text: std.ArrayList(u8),

    pub fn init(alloc: std.mem.Allocator) File {
        return .{
            .text = std.ArrayList(u8).init(alloc),
        };
    }

    pub fn deinit(self: *File) void {
        self.text.deinit();
    }

    pub fn writeLabel(self: *File, label: File.Label) !void {
        var wrt = self.text.writer();
        try wrt.print("L{x}:\n", .{label});
    }

    pub fn writeInstr(self: *File, instr: []const u8, args: []const Arg) !void {
        var wrt = self.text.writer();
        try wrt.writeAll('\t');
        try wrt.print("{s} ", .{instr});
        for (args, 0..) |arg, i| {
            switch (arg) {
                .Reg => |reg| try wrt.print("%{s}", .{@tagName(reg)}),
                .Imm => |imm| try wrt.print("${x}", .{imm}),
                .Label => |label| try wrt.print("L{x}", .{label}),
            }
            if (i + 1 != args.len) try wrt.writeAll(", ");
        }
        try wrt.writeByte('\n');
    }
};

pub const Stack = struct {
    offset: u32, // from frame base
};

const Loc = union(enum) {
    Reg: Reg,
    Stack: Stack,
    Comptime,
};

pub const Value = union(enum) {
    Owned: Loc,
    Borrowed: usize,
    None,
};

const Scope = struct {
    pub const Frame = usize;

    pub const Slot = struct {
        loc: Loc = .Comptime,
        type: Type.Id = Type.void_lit,
    };

    slots: []Slot,
    max_slot: usize = 0,
    regs: RegAlloc = .{},
    ret: Type.Id = Type.void_lit,

    pub fn init(alloc: std.mem.Allocator, peak_slot_count: usize) !Scope {
        return Scope{
            .slots = try alloc.alloc(Slot, peak_slot_count),
        };
    }

    pub fn deinit(self: *Scope, alloc: std.mem.Allocator) void {
        alloc.free(self.slots);
    }

    pub fn clear(self: *Scope, ret: Type.Id) void {
        self.regs = .{};
        for (self.slots) |*slot| slot.* = .{};
        self.max_slot = 0;
        self.ret = ret;
    }

    pub fn pushFrame(self: *Scope) Frame {
        return self.max_slot;
    }

    pub fn popFrame(self: *Scope, frame: Frame) void {
        for (0..self.max_slot - frame) |ri| {
            const i = self.max_slot - ri - 1;
            const slot = &self.slots[i];
            switch (slot.loc) {
                .Reg => |reg| self.regs.free(reg),
                .Stack => {},
                .Comptime => {},
            }
            slot.loc = .Comptime;
        }

        self.max_slot = frame;
    }
};

const Error = error{} || std.mem.Allocator.Error;

label_count: File.Label,
funcs: []File.Func,
ast: *const Ast,
types: *const Types,
file: *File,
scope: *Scope,

pub fn generate(alloc: std.mem.Allocator, ast: *const Ast, types: *const Types) Error!File {
    var file = File.init(alloc);

    var peak_slot_count: usize = 0;
    for (types.funcs) |func| peak_slot_count = @max(peak_slot_count, func.peak_slot_count);
    var scope = try Scope.init(alloc, peak_slot_count);
    defer scope.deinit(alloc);

    const funcs = try alloc.alloc(File.Func, types.funcs.len);
    defer alloc.free(funcs);
    for (funcs, 0..) |*func, i| func.label = @intCast(i);

    var self = Self{
        .label_count = @intCast(funcs.len),
        .funcs = funcs,
        .ast = ast,
        .types = types,
        .file = &file,
        .scope = &scope,
    };

    try self.gen();

    return file;
}

fn gen(self: *Self) Error!void {
    for (self.ast.items.items) |item| {
        switch (self.ast.item_store.get(item)) {
            .Func => |f| try self.genFunc(f, item.index),
        }
    }
}

fn genFunc(self: *Self, func: Ast.Item.Func, label: File.Label) Error!void {
    const ret = self.types.getValue(func.ret).data.type;

    if (func.params.len > 0) @panic("TODO: function parameters");
    if (!ret.eql(Type.usize_lit)) @panic("TODO: function return type");

    self.scope.clear(ret);
    try self.file.writeLabel(label);
    try self.genBlock(func.body);
}

fn genBlock(self: *Self, block: Ast.Expr.Block) Error!Value {
    const frame = self.scope.pushFrame();
    for (block) |expr| _ = try self.genExpr(self.ast.expr_store.get(expr));
    self.scope.popFrame(frame);
}

fn genExpr(self: *Self, expr: Ast.Expr) Error!Value {
    switch (expr) {
        .Var => |v| try self.genVar(v),
        inline else => |v, t| std.debug.panic("TODO: {any} {any}", .{ t, v }),
    }
}

fn genVar(self: *Self, variable: Ast.Expr.Var) Error!void {
    const value = self.types.getValue(variable.init);
    if (!value.is_runtime) return;

    const rt_value = self.genExpr(variable.init);
    _ = rt_value;

    unreachable;
}

fn allocLabel(self: *Self) File.Label {
    defer self.label_count += 1;
    return self.label_count;
}

test "sanity" {
    const alloc = std.testing.allocator;
    const src =
        \\fn main() usize {
        \\    var i = 1 + 2;
        \\    var j = i + 3;
        \\    var k = j + 4;
        \\    return k;
        \\}
    ;

    var ast = try Parser.parse(alloc, src);
    defer ast.deinit(alloc);
    var types = try Typechk.typecheck(alloc, &ast);
    defer types.deinit(alloc);

    var file = try generate(alloc, &ast, &types);
    defer file.deinit();

    std.log.warn("{s}", .{file.text.items});
}
