const std = @import("std");
const EnumList = @import("EnumList.zig");
const Parser = @import("Parser.zig");
const Ast = Parser.Ast;
const Typechk = @import("Typechk.zig");
const Types = Typechk.Module;
const Type = Typechk.Type;

pub const EmmitConfig = struct {
    entry: []const u8 = "main",
    ommit_frame_pointer: bool = false,
};

fn Emmiter(comptime W: type) type {
    return struct {
        const EThis = @This();

        writer: W,
        stack_size: u32,
        epilogue: Label,
        config: EmmitConfig,
        regs: RegAlloc.UsedIter,

        pub fn init(writer: W, epilogue: Label, stack_size: u32, regs: RegAlloc.UsedIter, config: EmmitConfig) EThis {
            return .{
                .writer = writer,
                .epilogue = epilogue,
                .stack_size = stack_size,
                .config = config,
                .regs = regs,
            };
        }

        pub fn writePrologue(self: *EThis) !void {
            var used_regs = self.regs;
            while (used_regs.next()) |reg| {
                try self.writer.writeAll("    ");
                try (Instr{ .Push = .{ .Reg = reg } }).write(self.stack_size, self.writer);
                try self.writer.writeByte('\n');
            }

            if (!self.config.ommit_frame_pointer) {
                try self.writeLine("push rbp");
                try self.writeLine("mov rbp, rsp");
            }

            if (self.stack_size > 0)
                try self.printLine("sub rsp, x0{x}", .{self.stack_size});
        }

        pub fn writeEpilogue(self: *EThis) !void {
            try self.writeLabel(self.epilogue);
            if (!self.config.ommit_frame_pointer) {
                try self.writeLine("mov rsp, rbp");
                try self.writeLine("pop rbp");
            } else if (self.stack_size > 0) {
                try self.printLine("add rsp, x0{x}", .{self.stack_size});
            }

            var used_regs = self.regs;
            while (used_regs.nextBack()) |reg| {
                try self.writer.writeAll("    ");
                try (Instr{ .Pop = .{ .Reg = reg } }).write(self.stack_size, self.writer);
                try self.writer.writeByte('\n');
            }

            try self.writeLine("ret");
        }

        pub fn writeFnLabel(self: *EThis, label: Label) !void {
            if (label == 0) {
                try self.writer.print("{s}:\n", .{self.config.entry});
            } else {
                try self.writer.print("fn_{x}:\n", .{label});
            }
        }

        pub fn writeInstrs(self: *EThis, instrs: []Instr) !void {
            for (instrs) |instr| {
                if (instr == .Ret) {
                    try self.printLine("jmp L{x}", .{self.epilogue});
                    continue;
                }
                try self.writer.writeAll("    ");
                try instr.write(self.stack_size, self.writer);
                try self.writer.writeAll("\n");
            }
        }

        fn writeLabel(self: *EThis, label: Label) !void {
            try self.writer.print("L{x}:\n", .{label});
        }

        fn writeLine(self: *EThis, line: []const u8) !void {
            try self.writer.print("    {s}\n", .{line});
        }

        fn printLine(self: *EThis, comptime fmt: []const u8, args: anytype) !void {
            try self.writer.writeAll("    ");
            try self.writer.print(fmt, args);
            try self.writer.writeByte('\n');
        }
    };
}

pub const Instr = union(enum) {
    const Binary = struct {
        dst: Value,
        src: Value,

        pub fn write(self: Binary, ctx: anytype) !void {
            try self.dst.write(ctx);
            try ctx.writer.writeAll(", ");
            try self.src.write(ctx);
        }
    };

    Mov: Binary,
    Add: Binary,
    Sub: Binary,
    Inc: Value,
    Dec: Value,
    Push: Value,
    Pop: Value,
    Call: Label,
    Ret,

    pub fn write(self: Instr, stack_size: usize, writer: anytype) !void {
        switch (self) {
            inline else => |v, t| {
                const name = @tagName(t);
                comptime var low_name: [name.len]u8 = undefined;
                inline for (&low_name, name) |*d, s| d.* = comptime std.ascii.toLower(s);
                try writer.writeAll(&low_name);

                if (@TypeOf(v) == void) return;

                try writer.writeByte(' ');

                if (@TypeOf(v) == Label) {
                    try writer.print("fn_{x}", .{v});
                } else {
                    try v.write(.{
                        .stack_size = stack_size,
                        .writer = writer,
                    });
                }
            },
        }
    }
};

pub const Reg = enum {
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

    pub const Set = std.meta.Int(.unsigned, count);

    pub const count = std.meta.fields(Reg).len;
    pub const caller_saved = makeSet(&.{ .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11 });
    pub const callee_saved = makeSet(&.{ .rbx, .rbp, .r12, .r13, .r14, .r15 });
    pub const reserved = makeSet(&.{ .rax, .rsp, .rbp });
    pub const args = [_]Reg{ .rdi, .rsi, .rdx, .rcx, .r8, .r9 };
    pub const arg_set = makeSet(args);

    pub fn makeSet(regs: []const Reg) Set {
        var mask: u16 = 0;
        for (regs) |reg| mask |= @as(u16, 1) << @intFromEnum(reg);
        return mask;
    }

    pub fn write(self: @This(), ctx: anytype) !void {
        try ctx.writer.writeAll(@tagName(self));
    }
};

pub const Label = u32;

pub const Value = union(enum) {
    const Stack = packed struct(u64) {
        offset: u31,
        pushed: bool,
        ref: u32 = ~@as(u32, 0),

        pub fn write(self: @This(), ctx: anytype) !void {
            const offset = if (self.pushed) self.offset + ctx.stack_size else self.offset;
            try ctx.writer.print("[rbp - 0x{x}]", .{offset});
        }
    };

    const Spilled = struct {
        reg: Reg,
        spill: Scope.Ref,

        pub fn write(self: @This(), ctx: anytype) !void {
            try self.reg.write(ctx);
        }
    };

    Reg: Reg,
    Stack: Stack,
    Spilled: Spilled,
    Imm: u64,

    pub fn write(self: Value, ctx: anytype) !void {
        switch (self) {
            .Reg => |r| try r.write(ctx),
            .Stack => |s| try s.write(ctx),
            .Spilled => |s| try s.write(ctx),
            .Imm => |i| try ctx.writer.print("0x{x}", .{i}),
        }
    }

    pub fn spill(self: *Value, stack_offset: u32) Reg {
        const offset: u31 = @intCast(stack_offset);
        const reg = switch (self.*) {
            .Reg => |r| r,
            .Spilled => |s| s.reg,
            else => unreachable,
        };
        switch (self.*) {
            .Reg => self.* = .{ .Stack = .{ .offset = offset, .pushed = true } },
            .Spilled => |s| self.* = .{ .Stack = .{ .offset = offset, .pushed = true, .ref = @intCast(s.spill.index) } },
            else => unreachable,
        }
        return reg;
    }

    pub fn restore(self: *Value, reg: Reg) void {
        switch (self.*) {
            .Stack => |s| if (s.ref == ~@as(u32, 0)) {
                self.* = .{ .Reg = reg };
            } else {
                self.* = .{ .Spilled = .{ .reg = reg, .spill = .{ .index = @intCast(s.ref) } } };
            },
            else => unreachable,
        }
    }
};

const RegAlloc = struct {
    const UsedIter = struct {
        used: Reg.Set,

        pub fn next(self: *UsedIter) ?Reg {
            const pos = @ctz(self.used);
            if (pos == Reg.count) return null;
            const bit = one << @intCast(pos);
            self.used &= ~bit;
            return @enumFromInt(pos);
        }

        pub fn nextBack(self: *UsedIter) ?Reg {
            var pos = @clz(self.used);
            if (pos == Reg.count) return null;
            pos = 15 - pos;
            const bit = one << @intCast(pos);
            self.used &= ~bit;
            return @enumFromInt(pos);
        }
    };

    const one: Reg.Set = 1;

    allocated: Reg.Set = Reg.reserved,
    used: Reg.Set = 0,
    locations: [Reg.count]?Scope.Ref = [_]?Scope.Ref{null} ** Reg.count,
    spill_ring: u4 = 0,

    pub fn alloc(self: *RegAlloc, to: Scope.Ref) ?Reg {
        var pos = @clz(~self.allocated);
        if (pos == Reg.count) return null;
        pos = 15 - pos;
        const bit = one << @intCast(pos);
        self.allocated |= bit;
        self.used |= bit & Reg.callee_saved;
        self.locations[pos] = to;
        return @enumFromInt(pos);
    }

    pub fn allocSpecific(self: *RegAlloc, to: Scope.Ref, reg: Reg) ?Scope.Ref {
        const pos = @intFromEnum(reg);
        const bit = one << @intCast(pos);
        self.allocated |= bit;
        self.used |= bit & Reg.callee_saved;
        defer self.locations[pos] = to;
        return self.locations[pos];
    }

    pub fn free(self: *RegAlloc, reg: Reg) void {
        const pos = @intFromEnum(reg);
        const bit = one << @intCast(pos);
        std.debug.assert(self.allocated & bit != 1);
        self.allocated &= ~bit;
        self.locations[pos] = null;
    }

    pub fn spill(self: *RegAlloc, to: Scope.Ref) Value.Spilled {
        self.spill_ring = @addWithOverflow(self.spill_ring, 1)[0];
        var bit = one << @intCast(self.spill_ring);
        while (Reg.reserved & bit != 0) {
            self.spill_ring = @addWithOverflow(self.spill_ring, 1)[0];
            bit = one << @intCast(self.spill_ring);
        }
        defer self.locations[self.spill_ring] = to;
        return .{ .reg = @enumFromInt(self.spill_ring), .spill = self.locations[self.spill_ring].? };
    }

    pub fn restore(self: *RegAlloc, reg: Reg, from: Scope.Ref) void {
        const pos = @intFromEnum(reg);
        self.locations[pos] = from;
    }

    pub fn usedIter(self: *const RegAlloc) UsedIter {
        return .{ .used = self.used };
    }
};

pub const FuncBuilder = struct {
    const default_spill = Reg.r12;

    instrs: std.ArrayList(Instr),
    stack_size: u32 = 0,
    pushed_stack_size: u32 = 0,
    peak_stack_size: u32 = 0,
    label_count: Label,

    pub fn init(alloc: std.mem.Allocator, first_label: Label) FuncBuilder {
        return .{ .instrs = std.ArrayList(Instr).init(alloc), .label_count = first_label };
    }

    pub fn deinit(self: *FuncBuilder) void {
        self.instrs.deinit();
    }

    pub fn allocLabel(self: *FuncBuilder) Label {
        defer self.label_count += 1;
        return self.label_count;
    }

    pub fn allocStack(self: *FuncBuilder, size: u32) u32 {
        defer self.stack_size += size;
        return self.stack_size;
    }

    pub fn freeStack(self: *FuncBuilder, size: u32) u32 {
        self.peak_stack_size = @max(self.peak_stack_size, self.stack_size);
        defer self.stack_size -= size;
        return self.stack_size;
    }

    pub fn pushStack(self: *FuncBuilder, size: u32) u32 {
        defer self.pushed_stack_size += size;
        return self.pushed_stack_size;
    }

    pub fn popStack(self: *FuncBuilder, size: u32) u32 {
        defer self.pushed_stack_size -= size;
        return self.pushed_stack_size;
    }

    pub fn pushInstr(self: *FuncBuilder, insrt: Instr) !void {
        try self.instrs.append(insrt);
    }

    pub fn emmit(self: *FuncBuilder, writer: anytype, func_id: Label, regs: RegAlloc.UsedIter, config: EmmitConfig) !void {
        std.debug.assert(self.pushed_stack_size == 0);
        var epilogue_label = self.allocLabel();
        var emmiter = Emmiter(@TypeOf(writer)).init(writer, epilogue_label, self.stack_size, regs, config);

        try emmiter.writeFnLabel(func_id);
        try emmiter.writePrologue();
        try emmiter.writeInstrs(self.instrs.items);
        try emmiter.writeEpilogue();
    }

    pub fn clear(self: *FuncBuilder) void {
        self.instrs.items.len = 0;
        self.stack_size = 0;
    }
};

const Scope = struct {
    pub const Frame = struct {
        symbol_len: usize,
        spill_len: usize,
    };

    pub const Symbol = struct {
        ident: Ast.Ident,
        ref: Ref,
    };

    pub const Slot = struct {
        value: Value,
        type: Type.Id,
        temorary: bool,
    };

    pub const Ref = struct {
        index: usize,
    };

    symbols: std.ArrayList(Symbol),
    ret: Type.Id = Type.void_lit,
    slots: std.ArrayList(Slot),

    pub fn init(alloc: std.mem.Allocator) Scope {
        return Scope{
            .symbols = std.ArrayList(Symbol).init(alloc),
            .slots = std.ArrayList(Slot).init(alloc),
        };
    }

    pub fn deinit(self: *Scope) void {
        self.symbols.deinit();
        self.slots.deinit();
    }

    pub fn clear(self: *Scope, ret: Type.Id) void {
        self.symbols.items.len = 0;
        self.ret = ret;
    }

    pub fn pushFrame(self: *Scope) Frame {
        return .{
            .symbol_len = self.symbols.items.len,
            .spill_len = self.slots.items.len,
        };
    }

    pub fn addSlot(self: *Scope, slot: Slot) std.mem.Allocator.Error!Ref {
        const index = self.slots.items.len;
        try self.slots.append(slot);
        return .{ .index = index };
    }

    pub fn findSymbol(self: *Scope, ident: Ast.Ident) ?Symbol {
        for (0..self.symbols.items.len) |ri| {
            const i = self.symbols.items.len - ri - 1;
            const sym = self.symbols.items[i];
            if (sym.ident.eql(ident)) return sym;
        }
        return null;
    }

    pub fn addSymbol(self: *Scope, value: Symbol) std.mem.Allocator.Error!void {
        try self.symbols.append(value);
    }

    pub fn nextSlot(self: *Scope) Ref {
        return .{ .index = self.slots.items.len };
    }

    pub fn getSlot(self: *Scope, ref: Ref) *Slot {
        return &self.slots.items[ref.index];
    }

    pub fn popFrame(self: *Scope, frame: Frame, comptime shift_last_slot: bool) if (shift_last_slot) Ref else void {
        if (shift_last_slot) {
            std.mem.swap(Slot, &self.slots.items[frame.spill_len], &self.slots.items[self.slots.items.len - 1]);
        }

        self.symbols.items.len = frame.symbol_len;
        self.slots.items.len = frame.spill_len + @intFromBool(shift_last_slot);

        if (shift_last_slot) return .{ .index = frame.spill_len };
    }
};

const Error = error{} || std.mem.Allocator.Error;
const InnerError = error{Returned} || Error;

const Self = @This();

ast: *const Ast,
types: *const Types,
source: []const u8,
scope: *Scope,
fb: *FuncBuilder,
regs: RegAlloc = .{},

pub fn generate(alloc: std.mem.Allocator, ast: *const Ast, types: *const Types, source: []const u8, writer: anytype) !void {
    var scope = Scope.init(alloc);
    defer scope.deinit();

    const max_funcs = ast.item_store.approxCountFor(Ast.Item.Func);
    var fb = FuncBuilder.init(alloc, @intCast(max_funcs));
    defer fb.deinit();

    var self = Self{
        .ast = ast,
        .types = types,
        .source = source,
        .scope = &scope,
        .fb = &fb,
    };

    try self.gen(writer);
}

fn gen(self: *Self, writer: anytype) !void {
    for (self.types.reached_functions) |item| {
        switch (self.ast.item_store.get(item)) {
            .Func => |f| {
                try self.genFunc(f);
                try self.fb.emmit(writer, item.index, self.regs.usedIter(), .{});
                self.regs = .{};
                self.fb.clear();
            },
        }
    }
}

fn genFunc(self: *Self, func: Ast.Item.Func) Error!void {
    const ret = self.types.getValue(func.ret).data.type;

    self.scope.clear(ret);

    if (!ret.eql(Type.usize_lit)) @panic("TODO: function return type");
    //if (func.params.len > 0) @panic("TODO: function parameters");
    for (func.params, Reg.args[0..func.params.len]) |param, reg| {
        const value = self.types.getValue(param.type);
        const ref = self.scope.nextSlot();
        std.debug.assert(self.regs.allocSpecific(ref, reg) == null);
        _ = try self.scope.addSlot(.{
            .value = .{ .Reg = reg },
            .type = value.type,
            .temorary = false,
        });
        try self.scope.addSymbol(.{ .ident = param.name, .ref = ref });
    }

    _ = self.genBlock(func.body) catch |err| switch (err) {
        error.Returned => {},
        else => |e| return e,
    };
}

fn genBlock(self: *Self, block: Ast.Expr.Block) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();
    for (block) |expr| {
        _ = try self.genExpr(expr);
    }
    try self.popFrame(frame, false);
    return null;
}

fn genExpr(self: *Self, expr: Ast.Expr.Id) InnerError!?Scope.Ref {
    const value = self.types.getValue(expr);
    if (!value.is_runtime) {
        if (value.type.eql(Type.void_lit)) return null;
        if (value.type.tag == .Int) return try self.scope.addSlot(.{
            .value = .{ .Imm = value.data.int },
            .type = self.types.getValue(expr).type,
            .temorary = false,
        });
    }

    return switch (self.ast.expr_store.get(expr)) {
        .Var => |v| try self.genVar(v),
        .Ret => |r| try self.genRet(r),
        .Binary => |b| try self.genBinary(b),
        .Ident => |i| try self.genIdent(i),
        .Int => |i| try self.scope.addSlot(.{
            .value = .{ .Imm = i },
            .type = self.types.getValue(expr).type,
            .temorary = false,
        }),
        .Call => |c| try self.genCall(c),
        inline else => |v, t| std.debug.panic("TODO: {any} {any}", .{ t, v }),
    };
}

fn genCall(self: *Self, c: Ast.Expr.Call) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();
    try self.prepareCall(c.args);

    const func = self.types.getValue(c.callee).data.decl;
    const label = func.index;
    try self.fb.pushInstr(.{ .Call = label });

    try self.popFrame(frame, false);

    const ref = try self.allocRegPush(self.scope.ret, true);
    try self.fb.pushInstr(.{ .Mov = .{ .dst = self.scope.getSlot(ref).value, .src = .{ .Reg = .rax } } });

    return ref;
}

fn allocRegPush(self: *Self, ty: Type.Id, temporary: bool) !Scope.Ref {
    const ref = self.scope.nextSlot();
    if (self.regs.alloc(ref)) |reg| {
        return try self.scope.addSlot(.{ .value = .{ .Reg = reg }, .type = ty, .temorary = temporary });
    }

    const target = self.regs.spill(ref);
    try self.fb.pushInstr(.{ .Push = .{ .Reg = target.reg } });
    std.debug.assert(self.scope.getSlot(target.spill).value.spill(self.fb.pushStack(8)) == target.reg);
    return try self.scope.addSlot(.{
        .value = .{ .Spilled = target },
        .type = ty,
        .temorary = temporary,
    });
}

fn allocRegPushSpecific(self: *Self, ty: Type.Id, reg: Reg) !Scope.Ref {
    const ref = self.scope.nextSlot();
    if (self.regs.allocSpecific(ref, reg)) |current| {
        std.debug.assert(switch (self.scope.getSlot(current).value) {
            .Imm => false,
            .Reg => |r| reg == r,
            .Stack => false,
            .Spilled => |p| reg == p.reg,
        });
        try self.fb.pushInstr(.{ .Push = self.scope.getSlot(current).value });
        _ = try self.scope.addSlot(.{
            .value = .{ .Spilled = .{ .reg = reg, .spill = current } },
            .type = ty,
            .temorary = true,
        });
        std.debug.assert(self.scope.getSlot(current).value.spill(self.fb.pushStack(8)) == reg);
    } else {
        _ = try self.scope.addSlot(.{
            .value = .{ .Reg = reg },
            .type = ty,
            .temorary = true,
        });
    }
    return ref;
}

fn prepareCall(self: *Self, args: []const Ast.Expr.Id) InnerError!void {
    for (args, Reg.args[0..args.len]) |arg, reg| {
        const value = (try self.genExpr(arg)).?;
        const loc = self.scope.getSlot(value).value;
        const regv = try self.allocRegPushSpecific(self.scope.getSlot(value).type, reg);
        try self.fb.pushInstr(.{ .Mov = .{
            .dst = self.scope.getSlot(regv).value,
            .src = loc,
        } });
    }
}

fn genBinary(self: *Self, b: Ast.Expr.Binary) InnerError!?Scope.Ref {
    return switch (b.op) {
        .Add, .Sub => try self.genMathOp(b),
        .Assign => try self.genAssign(b),
    };
}

fn genMathOp(self: *Self, b: Ast.Expr.Binary) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();

    var lhs = (try self.genExpr(b.lhs)).?;
    const rhs = (try self.genExpr(b.rhs)).?;

    if (!self.scope.getSlot(lhs).temorary) {
        const ref = try self.allocRegPush(self.scope.getSlot(lhs).type, true);
        try self.fb.pushInstr(.{ .Mov = .{
            .dst = self.scope.getSlot(ref).value,
            .src = self.scope.getSlot(lhs).value,
        } });
        lhs = ref;
    }

    const lhs_loc = self.scope.getSlot(lhs).value;
    const rhs_loc = self.scope.getSlot(rhs).value;

    switch (b.op) {
        .Add => try self.fb.pushInstr(.{ .Add = .{ .dst = lhs_loc, .src = rhs_loc } }),
        .Sub => try self.fb.pushInstr(.{ .Sub = .{ .dst = lhs_loc, .src = rhs_loc } }),
        else => unreachable,
    }

    return try self.popFrame(frame, true);
}

fn genAssign(self: *Self, binary: Ast.Expr.Binary) InnerError!?Scope.Ref {
    const target = (try self.genExpr(binary.lhs)).?;

    if (self.scope.getSlot(target).value == .Imm) {
        const new = try self.allocRegPush(self.scope.getSlot(target).type, false);
        try self.fb.pushInstr(.{ .Mov = .{
            .dst = self.scope.getSlot(new).value,
            .src = self.scope.getSlot(target).value,
        } });
        self.scope.getSlot(target).value = self.scope.getSlot(new).value;
        switch (self.scope.getSlot(target).value) {
            .Reg => |r| self.regs.restore(r, target),
            .Spilled => |p| self.regs.restore(p.reg, target),
            else => {},
        }
        self.scope.slots.items.len -= 1;
    }

    const value = (try self.genExpr(binary.rhs)).?;
    const target_loc = self.scope.getSlot(target).value;
    const value_loc = self.scope.getSlot(value).value;

    try self.fb.pushInstr(.{ .Mov = .{ .dst = target_loc, .src = value_loc } });

    return null;
}

fn genIdent(self: *Self, ident: Ast.Ident) InnerError!?Scope.Ref {
    return self.scope.findSymbol(ident).?.ref;
}

fn genVar(self: *Self, variable: Ast.Expr.Var) InnerError!?Scope.Ref {
    const rt_value = (try self.genExpr(variable.init)).?;
    try self.scope.addSymbol(.{ .ident = variable.name, .ref = rt_value });
    return null;
}

fn genRet(self: *Self, ret: Ast.Expr.Id) InnerError!?Scope.Ref {
    const value = (try self.genExpr(ret)).?;
    const loc = self.scope.getSlot(value).value;
    try self.fb.pushInstr(.{ .Mov = .{ .dst = .{ .Reg = .rax }, .src = loc } });
    try self.popFrame(.{ .spill_len = 0, .symbol_len = 0 }, false);
    try self.fb.pushInstr(.Ret);
    return InnerError.Returned;
}

fn popFrame(self: *Self, frame: Scope.Frame, comptime shift_last_slot: bool) !if (shift_last_slot) Scope.Ref else void {
    for (0..self.scope.slots.items.len - @intFromBool(shift_last_slot) - frame.spill_len) |ri| {
        const i = self.scope.slots.items.len - ri - 1 - @intFromBool(shift_last_slot);
        const slot = self.scope.slots.items[i];
        switch (slot.value) {
            .Imm => {},
            .Reg => |r| self.regs.free(r),
            .Stack => |s| if (!s.pushed) {
                _ = self.fb.freeStack(8);
            },
            .Spilled => |p| {
                _ = self.fb.popStack(8);
                try self.fb.pushInstr(.{ .Pop = .{ .Reg = p.reg } });
                self.regs.restore(p.reg, p.spill);
                self.scope.getSlot(p.spill).value.restore(p.reg);
            },
        }
    }

    const new_loc = self.scope.popFrame(frame, shift_last_slot);

    if (shift_last_slot) {
        const slot = self.scope.getSlot(new_loc);
        switch (slot.value) {
            .Imm => {},
            .Reg => |r| self.regs.restore(r, new_loc),
            .Stack => {},
            .Spilled => |*p| self.regs.restore(p.reg, new_loc),
        }
    }

    return new_loc;
}

test "sanity" {
    const alloc = std.testing.allocator;
    const src =
        \\fn main() usize {
        \\    const i = 1 + 2;
        \\    const j = i + 3;
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    var k: usize = j;
        \\    k = k + 5 + foo(4);
        \\    return k;
        \\}
        \\
        \\fn foo(a: usize) usize {
        \\    return a + a + 4;
        \\}
    ;

    var ast = try Parser.parse(alloc, src);
    defer ast.deinit(alloc);
    for (ast.errors.items) |err| std.log.warn("{any}", .{err});
    try std.testing.expect(ast.errors.items.len == 0);
    try std.testing.expect(ast.items.items.len == 2);

    // var buffer = [1]u8{0} ** 10000;
    // var st = std.io.fixedBufferStream(&buffer);
    // var wr = st.writer();
    // var printer = Parser.Printer(@TypeOf(wr)).init(&ast, wr, src);
    // try printer.print();

    // std.log.warn("{s}", .{buffer});

    var types = try Typechk.check(alloc, &ast, src);
    defer types.deinit(alloc);

    const file_name = "test.asm";
    const obj_name = "test.o";
    var local_file = try std.fs.cwd().createFile(file_name, .{});
    defer local_file.close();
    var writer = local_file.writer();

    try writer.writeAll(
        \\    global main
        \\
        \\    section .text
        \\
    );

    try generate(alloc, &ast, &types, src, writer);

    try run(alloc, &.{ "/usr/bin/nasm", file_name, "-felf64", "-o", obj_name }, 0);
    try run(alloc, &.{ "/usr/bin/gcc", "-o", "test", obj_name }, 0);
    try run(alloc, &.{"./test"}, 23);
}

fn run(alloc: std.mem.Allocator, args: []const []const u8, expected: u8) !void {
    var child = std.ChildProcess.init(args, alloc);
    const res = try child.spawnAndWait();
    try std.testing.expect(res.Exited == expected);
}
