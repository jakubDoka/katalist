const std = @import("std");
const EnumList = @import("EnumList.zig");
const Parser = @import("Parser.zig");
const Ast = @import("Parser/Ast.zig");
const Typechk = @import("Typechk.zig");
const Module = Typechk.Module;
const Type = Typechk.Type;
const garbage = @import("garbage.zig");
//const RegAlloc = @import("Codegen/RegAlloc.zig");

pub const EmmitConfig = struct {
    entry: []const u8 = "main",
    ommit_frame_pointer: bool = false,
};

fn declLabel(self: Label, writer: anytype, main: []const u8) !void {
    if (self == 0) {
        try writer.print("{s}:\n", .{main});
    } else {
        try writer.print("L{x}:\n", .{self});
    }
}

fn useLabel(self: Label, writer: anytype) !void {
    try writer.print("L{x}", .{self});
}

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
            while (used_regs.next()) |reg| try self.writer.print("    push {s}\n", .{@tagName(reg)});

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
            while (used_regs.nextBack()) |reg| try self.writer.print("    pop {s}\n", .{@tagName(reg)});

            try self.writeLine("ret");
        }

        pub fn writeLabel(self: *EThis, label: Label) !void {
            try declLabel(label, self.writer, self.config.entry);
        }

        pub fn writeInstrs(self: *EThis, instrs: []FuncBuilder.TypedInstr, types: *const Module) !void {
            for (instrs) |ty| {
                if (ty.instr == .Ret) {
                    try self.printLine("jmp L{x}", .{self.epilogue});
                    continue;
                }
                try self.writeInstr(ty, types);
            }
        }

        fn writeInstr(self: *EThis, ty: FuncBuilder.TypedInstr, types: *const Module) !void {
            var ctx = .{
                .stack_size = self.stack_size,
                .entrypoint = self.config.entry,
                .writer = self.writer,
                .types = types,
                .type = ty.type,
            };

            try self.writer.writeAll("    ");
            try ty.instr.write(&ctx);
            try self.writer.writeAll("\n");
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

    const Set = struct {
        const Cc = enum {
            e,
            ne,
            l,
            g,
            le,
            ge,
        };

        dst: Reg,
        cc: Cc,

        pub fn writeFull(self: Set, ctx: anytype) !void {
            try ctx.writer.print("set{s} {s}\n", .{ @tagName(self.cc), self.dst.asByteReg() });
            try ctx.writer.print("    movzx {s}, {s}", .{ @tagName(self.dst), self.dst.asByteReg() });
        }
    };

    Mov: Binary,
    Add: Binary,
    Sub: Binary,
    Cmp: Binary,
    Inc: Value,
    Dec: Value,
    Push: Value,
    Pop: Value,
    Call: Label,
    Jmp: Label,
    Je: Label,
    Label: Label,
    Set: Set,
    Ret,

    pub fn write(self: Instr, ctx: anytype) !void {
        switch (self) {
            .Label => |l| try ctx.writer.print("L{x}:", .{l}),
            inline else => |v, t| {
                const Ty = @TypeOf(v);

                if (Ty != void and Ty != Label and @hasDecl(Ty, "writeFull")) {
                    try v.writeFull(ctx);
                    return;
                }

                const name = @tagName(t);
                comptime var low_name: [name.len]u8 = undefined;
                inline for (&low_name, name) |*d, s| d.* = comptime std.ascii.toLower(s);
                try ctx.writer.writeAll(&low_name);

                if (Ty == void) return;

                try ctx.writer.writeByte(' ');

                if (Ty == Label) {
                    try useLabel(v, ctx.writer);
                } else {
                    try v.write(ctx);
                }
            },
        }
    }

    pub fn isUseless(self: *Instr) bool {
        switch (self.*) {
            .Add => |b| if (b.src == .Imm and b.src.Imm == 1) {
                self.* = .{ .Inc = b.dst };
            },
            .Sub => |b| if (b.src == .Imm and b.src.Imm == 1) {
                self.* = .{ .Dec = b.dst };
            },
            else => {},
        }

        return switch (self.*) {
            .Add, .Sub => |b| b.src == .Imm and b.src.Imm == 0,
            else => false,
        };
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
        const bitSize = ctx.types.bitSizeOf(ctx.type);
        try ctx.writer.writeAll(self.sizedName(bitSize));
    }

    pub fn asByteReg(self: Reg) []const u8 {
        return switch (self) {
            inline .rax, .rbx, .rcx, .rdx => |t| @tagName(t)[1..2] ++ "l",
            inline .rdi, .rsi, .rbp, .rsp => |t| @tagName(t)[1..] ++ "l",
            inline else => |t| @tagName(t) ++ "b",
        };
    }

    pub fn asWordReg(self: Reg) []const u8 {
        return switch (self) {
            inline .rax, .rbx, .rcx, .rdx, .rdi, .rsi, .rbp, .rsp => |t| @tagName(t)[1..],
            inline else => |t| @tagName(t) ++ "w",
        };
    }

    pub fn asDwordReg(self: Reg) []const u8 {
        return switch (self) {
            inline .rax, .rbx, .rcx, .rdx, .rdi, .rsi, .rbp, .rsp => |t| "e" ++ @tagName(t)[1..],
            inline else => |t| @tagName(t) ++ "d",
        };
    }

    pub fn sizedName(self: Reg, size: usize) []const u8 {
        return switch (size) {
            1...8 => self.asByteReg(),
            9...16 => self.asWordReg(),
            17...32 => self.asDwordReg(),
            33...64 => @tagName(self),
            else => std.debug.panic("TODO: {any}", .{size}),
        };
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
            std.debug.assert(offset != ~@as(u31, 0));
            try ctx.writer.print("[rbp - 0x{x}]", .{offset + 8});
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
    Moved,

    pub fn write(self: Value, ctx: anytype) !void {
        switch (self) {
            .Reg => |r| try r.write(ctx),
            .Stack => |s| try s.write(ctx),
            .Spilled => |s| try s.write(ctx),
            .Imm => |i| try ctx.writer.print("0x{x}", .{i}),
            .Moved => unreachable,
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
            else => |v| std.debug.panic("TODO: {any}", .{v}),
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
        std.debug.assert(self.allocated & bit != 0);
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
        const spl = self.locations[self.spill_ring].?;
        std.debug.assert(spl.index != to.index);
        return .{
            .reg = @enumFromInt(self.spill_ring),
            .spill = spl,
        };
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

    const TypedInstr = struct {
        instr: Instr,
        type: Type.Id,
    };

    instrs: std.ArrayList(TypedInstr),
    stack_size: u32 = 0,
    pushed_stack_size: u32 = 0,
    peak_stack_size: u32 = 0,
    label_count: Label,

    pub fn init(alloc: std.mem.Allocator, first_label: Label) FuncBuilder {
        return .{
            .instrs = std.ArrayList(TypedInstr).init(alloc),
            .label_count = first_label,
        };
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

    pub fn pushInstr(self: *FuncBuilder, ty: Type.Id, instr: Instr) !void {
        if (Type.decode(ty)) |t| std.debug.assert(!t.isComptime());
        var final_instr = instr;
        if (final_instr.isUseless()) return;
        try self.instrs.append(.{ .instr = final_instr, .type = ty });
    }

    pub fn pushInstrUntyped(self: *FuncBuilder, instr: Instr) !void {
        try self.pushInstr(Type.usize_lit, instr);
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
        borrow_len: usize,
        to_free_len: usize,
    };

    pub const Symbol = struct {
        ref: Ref,
    };

    pub const Slot = struct {
        value: Value,
        type: Type.Id,
        temorary: bool,
        borrowed: bool = false,
    };

    pub const Ref = struct {
        index: usize,
    };

    symbols: []Symbol,
    borrowed: std.ArrayList(Ref),
    to_free: std.ArrayList(Ref),
    ret: Type.Id = Type.void_lit,
    slots: std.ArrayList(Slot),

    pub fn init(alloc: std.mem.Allocator, buffer: []Symbol) Scope {
        return Scope{
            .symbols = buffer[0..0],
            .slots = std.ArrayList(Slot).init(alloc),
            .borrowed = std.ArrayList(Ref).init(alloc),
            .to_free = std.ArrayList(Ref).init(alloc),
        };
    }

    pub fn deinit(self: *Scope) void {
        self.slots.deinit();
        self.borrowed.deinit();
        self.to_free.deinit();
    }

    pub fn clear(self: *Scope, ret: Type.Id) void {
        self.symbols.len = 0;
        self.ret = ret;
    }

    pub fn pushFrame(self: *Scope) Frame {
        return .{
            .symbol_len = self.symbols.len,
            .spill_len = self.slots.items.len,
            .borrow_len = self.borrowed.items.len,
            .to_free_len = self.to_free.items.len,
        };
    }

    pub fn addSlot(self: *Scope, slot: Slot) std.mem.Allocator.Error!Ref {
        const index = self.slots.items.len;
        try self.slots.append(slot);
        return .{ .index = index };
    }

    pub fn findSymbol(self: *Scope, ident: Ast.Ident) ?Symbol {
        if (ident.unordered) return null;
        return self.symbols[ident.index];
    }

    pub fn addSymbol(self: *Scope, value: Symbol) std.mem.Allocator.Error!void {
        self.symbols.len += 1;
        self.symbols[self.symbols.len - 1] = value;
    }

    pub fn skipSimbol(self: *Scope) void {
        self.symbols.len += 1;
    }

    pub fn nextSlot(self: *Scope) Ref {
        return .{ .index = self.slots.items.len };
    }

    pub fn getSlot(self: *Scope, ref: Ref) *Slot {
        return &self.slots.items[ref.index];
    }

    pub fn popFrame(
        self: *Scope,
        frame: Frame,
        comptime shift_last_slot: bool,
    ) if (shift_last_slot) Ref else void {
        if (shift_last_slot) {
            std.mem.swap(Slot, &self.slots.items[frame.spill_len], &self.slots.items[self.slots.items.len - 1]);
        }

        self.to_free.items.len = frame.to_free_len;
        self.borrowed.items.len = frame.borrow_len;
        self.symbols.len = frame.symbol_len;
        self.slots.items.len = frame.spill_len + @intFromBool(shift_last_slot);

        if (shift_last_slot) return .{ .index = frame.spill_len };
    }
};

const Error = error{} || std.mem.Allocator.Error;
const InnerError = error{Returned} || Error;

const Self = @This();

ast: *const Ast,
module: *const Module,
types: *const Module.ReachedFunc = undefined,
exprs: Ast.Expr.Store.View = undefined,
source: []const u8,
scope: *Scope,
fb: *FuncBuilder,
regs: RegAlloc = .{},

pub fn generate(alloc: std.mem.Allocator, ast: *const Ast, types: *const Module, source: []const u8, writer: anytype) !void {
    const sym_buffer = try alloc.alloc(Scope.Symbol, ast.peak_sym_count);
    defer alloc.free(sym_buffer);
    var scope = Scope.init(alloc, sym_buffer);
    defer scope.deinit();

    const max_funcs = ast.items.query(.Func).len;
    var fb = FuncBuilder.init(alloc, @intCast(max_funcs));
    defer fb.deinit();

    var self = Self{
        .ast = ast,
        .module = types,
        .source = source,
        .scope = &scope,
        .fb = &fb,
    };

    try self.gen(writer);
}

fn gen(self: *Self, writer: anytype) !void {
    for (self.module.reached_functions) |*item| {
        const func = &self.ast.items.query(.Func)[item.index];
        self.types = item;
        self.exprs = self.ast.exprs.view(func.slice);
        try self.genFunc(func);

        std.debug.assert(self.fb.pushed_stack_size == 0);
        var epilogue_label = self.fb.allocLabel();
        var emmiter = Emmiter(@TypeOf(writer)).init(
            writer,
            epilogue_label,
            self.fb.stack_size,
            self.regs.usedIter(),
            .{},
        );

        try emmiter.writeLabel(@intCast(item.index));
        try emmiter.writePrologue();
        try emmiter.writeInstrs(self.fb.instrs.items, self.module);
        try emmiter.writeEpilogue();

        self.regs = .{};
        self.fb.clear();
    }
}

fn genFunc(self: *Self, func: *const Ast.Item.Func) Error!void {
    const ret = self.types.getValue(func.ret).data.type;

    self.scope.clear(ret);

    for (func.params, Reg.args[0..func.params.len]) |param, reg| {
        const value = self.types.getValue(param.type);
        const ref = self.scope.nextSlot();
        std.debug.assert(self.regs.allocSpecific(ref, reg) == null);
        _ = try self.scope.addSlot(.{
            .value = .{ .Reg = reg },
            .type = value.data.type,
            .temorary = false,
        });
        try self.scope.addSymbol(.{ .ref = ref });
    }

    _ = self.genBlock(func.body) catch |err| switch (err) {
        error.Returned => {},
        else => |e| return e,
    };
}

fn genBlock(self: *Self, block: Ast.Expr.Block) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();
    for (block) |expr| {
        _ = self.genExpr(expr) catch |err| switch (err) {
            error.Returned => {
                try self.popFrame(frame, false);
                return err;
            },
            else => |e| return e,
        };
    }
    try self.popFrame(frame, false);
    return null;
}

fn genExpr(self: *Self, expr: Ast.Expr.Id) InnerError!?Scope.Ref {
    const value = self.types.getValue(expr);
    if (!value.is_runtime) {
        if (expr.tag == .Var) self.scope.skipSimbol();
        if (value.type.eql(Type.void_lit)) return null;
        if (value.type.tag == .Bool) return try self.scope.addSlot(.{
            .value = .{ .Imm = @intFromBool(value.data.bool) },
            .type = self.types.getValue(expr).type,
            .temorary = false,
        });
        if (value.type.tag == .Int) return try self.scope.addSlot(.{
            .value = .{ .Imm = value.data.int },
            .type = self.types.getValue(expr).type,
            .temorary = false,
        });
    }

    return switch (self.exprs.get(expr)) {
        .Var => |v| try self.genVar(v),
        .Ret => |r| try self.genRet(r),
        .If => |i| try self.genIf(value, i),
        .Binary => |b| try self.genBinary(b),
        .Ident => |i| try self.genIdent(i),
        .Int => |i| try self.scope.addSlot(.{
            .value = .{ .Imm = i },
            .type = self.types.getValue(expr).type,
            .temorary = false,
        }),
        .Bool => |b| try self.scope.addSlot(.{
            .value = .{ .Imm = @intFromBool(b) },
            .type = self.types.getValue(expr).type,
            .temorary = false,
        }),
        .Call => |c| try self.genCall(c),
        .Parens => |p| try self.genExpr(p),
        inline else => |v, t| std.debug.panic("TODO: {any} {any}", .{ t, v }),
    };
}

fn genIf(self: *Self, value: Typechk.Value, i: Ast.Expr.If) InnerError!?Scope.Ref {
    _ = value;
    const cond_value = self.types.getValue(i.cond);
    if (!cond_value.is_runtime) {
        if (cond_value.data.bool) return try self.genScopedExpr(i.then);
        if (i.els) |e| return try self.genScopedExpr(e);
        return null;
    }

    const else_label = if (i.els != null) self.fb.allocLabel() else null;
    const end_label = self.fb.allocLabel();

    const cond = (try self.genExpr(i.cond)).?;
    try self.fb.pushInstr(Type.bool_lit, .{ .Cmp = .{ .dst = self.scope.getSlot(cond).value, .src = .{ .Imm = 0 } } });
    try self.fb.pushInstrUntyped(.{ .Je = else_label orelse end_label });

    if (self.genScopedExpr(i.then)) |then| {
        const els = i.els orelse {
            try self.pushLabel(end_label);
            return null;
        };

        const opt_ret = if (then) |th| try self.ensureTemporary(th) else null;
        try self.fb.pushInstrUntyped(.{ .Jmp = end_label });

        try self.pushLabel(else_label.?);
        const elsr = self.genScopedExpr(els) catch |err| switch (err) {
            error.Returned => return opt_ret,
            else => |e| return e,
        };

        const ret = opt_ret orelse return null;

        try self.pushMov(elsr.?, ret);
        try self.pushLabel(end_label);
        self.scope.slots.items.len -= 1;

        return ret;
    } else |err| switch (err) {
        error.Returned => {},
        else => |e| return e,
    }

    try self.pushLabel(else_label orelse end_label);
    const els = i.els orelse return null;
    const opt_elsr = self.genScopedExpr(els) catch |err| switch (err) {
        error.Returned => return null,
        else => |e| return e,
    };
    const elsr = opt_elsr orelse return null;
    const ret = try self.ensureTemporary(elsr);
    try self.pushLabel(end_label);

    return ret;
}

fn pushLabel(self: *Self, label: Label) !void {
    try self.fb.pushInstrUntyped(.{ .Label = label });
}

fn pushMov(self: *Self, scr: Scope.Ref, dst: Scope.Ref) !void {
    const src_loc = self.scope.getSlot(scr);
    const dst_loc = self.scope.getSlot(dst);
    try self.fb.pushInstr(
        dst_loc.type,
        .{ .Mov = .{ .dst = dst_loc.value, .src = src_loc.value } },
    );
}

fn ensureTemporary(self: *Self, ref: Scope.Ref) !Scope.Ref {
    const current = self.scope.getSlot(ref);
    if (current.temorary) return ref;
    const new = try self.allocRegPush(current.type, true);
    try self.pushMov(ref, new);
    return new;
}

fn genScopedExpr(self: *Self, expr: Ast.Expr.Id) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();
    const value = self.genExpr(expr) catch |err| switch (err) {
        error.Returned => {
            try self.popFrame(frame, false);
            return err;
        },
        else => |e| return e,
    };
    if (value != null) return try self.popFrame(frame, true);
    try self.popFrame(frame, false);
    return null;
}

fn genCall(self: *Self, c: Ast.Expr.Call) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();
    try self.prepareCall(c.args);

    const func = self.types.getValue(c.callee).data.decl;
    const label = func.index;
    try self.fb.pushInstrUntyped(.{ .Call = label });

    try self.popFrame(frame, false);

    const ref = try self.allocRegPush(self.scope.ret, true);
    const ref_loc = self.scope.getSlot(ref);
    try self.fb.pushInstr(ref_loc.type, .{ .Mov = .{
        .dst = ref_loc.value,
        .src = .{ .Reg = .rax },
    } });

    return ref;
}

fn allocRegPush(self: *Self, ty: Type.Id, temporary: bool) !Scope.Ref {
    const ref = self.scope.nextSlot();
    if (self.regs.alloc(ref)) |reg| {
        return try self.scope.addSlot(.{
            .value = .{ .Reg = reg },
            .type = ty,
            .temorary = temporary,
        });
    }

    const target = self.regs.spill(ref);
    try self.fb.pushInstr(ty, .{ .Push = .{ .Reg = target.reg } });
    std.debug.assert(self.scope.getSlot(target.spill)
        .value.spill(self.fb.pushStack(8)) == target.reg);
    return try self.scope.addSlot(.{
        .value = .{ .Spilled = target },
        .type = ty,
        .temorary = temporary,
    });
}

fn allocRegPushSpecific(self: *Self, ty: Type.Id, reg: Reg) !Scope.Ref {
    const ref = self.scope.nextSlot();
    if (self.regs.allocSpecific(ref, reg)) |current| {
        std.debug.assert(current.index != ref.index);
        const current_loc = self.scope.getSlot(current);
        std.debug.assert(switch (current_loc.value) {
            .Imm => false,
            .Reg => |r| reg == r,
            .Stack => false,
            .Spilled => |p| reg == p.reg,
            .Moved => false,
        });
        try self.fb.pushInstr(current_loc.type, .{ .Push = current_loc.value });
        _ = try self.scope.addSlot(.{
            .value = .{ .Spilled = .{ .reg = reg, .spill = current } },
            .type = ty,
            .temorary = false,
        });
        std.debug.assert(self.scope.getSlot(current)
            .value.spill(self.fb.pushStack(8)) == reg);
    } else {
        _ = try self.scope.addSlot(.{
            .value = .{ .Reg = reg },
            .type = ty,
            .temorary = false,
        });
    }
    return ref;
}

fn prepareCall(self: *Self, args: []const Ast.Expr.Id) InnerError!void {
    for (args, Reg.args[0..args.len]) |arg, reg| {
        const value = (try self.genExpr(arg)).?;
        const loc = self.scope.getSlot(value);
        if (loc.value == .Reg and loc.value.Reg == reg) continue;
        const regv = try self.allocRegPushSpecific(loc.type, reg);
        try self.pushMov(value, regv);
    }
}

fn genBinary(self: *Self, b: Ast.Expr.Binary) InnerError!?Scope.Ref {
    return switch (b.op) {
        .Add, .Sub => try self.genMathOp(b),
        .Eq, .Ne, .Lt, .Gt, .Le, .Ge => try self.genCmp(b),
        .Assign => try self.genAssign(b),
    };
}

fn genMathOp(self: *Self, b: Ast.Expr.Binary) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();

    const lhs = (try self.genExpr(b.lhs)).?;
    const rhs_frame = self.scope.pushFrame();
    const rhs = (try self.genExpr(b.rhs)).?;

    var lhs_slot = self.scope.getSlot(lhs);
    var rhs_slot = self.scope.getSlot(rhs);
    const swapped = !lhs_slot.temorary;

    if (swapped) {
        if (rhs_slot.temorary and b.op.isCommutative()) {
            std.mem.swap(*Scope.Slot, &lhs_slot, &rhs_slot);
        } else {
            lhs_slot = self.scope.getSlot(try self.ensureTemporary(lhs));
        }
    }

    const binary = Instr.Binary{ .dst = lhs_slot.value, .src = rhs_slot.value };
    try self.fb.pushInstr(lhs_slot.type, switch (b.op) {
        .Add => .{ .Add = binary },
        .Sub => .{ .Sub = binary },
        else => unreachable,
    });

    if (!swapped) try self.popFrame(rhs_frame, false);

    return try self.popFrame(frame, true);
}

fn genCmp(self: *Self, b: Ast.Expr.Binary) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();

    var lhs = (try self.genExpr(b.lhs)).?;
    var rhs = (try self.genExpr(b.rhs)).?;

    const ty = self.scope.getSlot(lhs).type;
    try self.fb.pushInstr(ty, .{ .Cmp = .{
        .dst = self.scope.getSlot(lhs).value,
        .src = self.scope.getSlot(rhs).value,
    } });

    const set: Instr.Set.Cc = switch (b.op) {
        .Eq => .e,
        .Ne => .ne,
        .Lt => .l,
        .Gt => .g,
        .Le => .le,
        .Ge => .ge,
        else => unreachable,
    };
    const ref = try self.allocRegPush(Type.bool_lit, true);
    try self.fb.pushInstrUntyped(.{ .Set = .{
        .dst = self.scope.getSlot(ref).value.Reg,
        .cc = set,
    } });

    return try self.popFrame(frame, true);
}

fn genAssign(self: *Self, binary: Ast.Expr.Binary) InnerError!?Scope.Ref {
    const frame = self.scope.pushFrame();

    const target = (try self.genExpr(binary.lhs)).?;
    const value = (try self.genExpr(binary.rhs)).?;

    try self.pushMov(value, target);

    try self.popFrame(frame, false);

    return null;
}

fn genIdent(self: *Self, ident: Ast.Ident) InnerError!?Scope.Ref {
    var ref = self.scope.findSymbol(ident).?.ref;

    const slot = self.scope.getSlot(ref);
    if (ident.last and slot.value == .Reg and !slot.borrowed) {
        ref = try self.scope.addSlot(.{
            .value = slot.value,
            .type = slot.type,
            .temorary = true,
        });
        slot.value = .Moved;
        slot.borrowed = true;
    } else if (ident.last and slot.value == .Reg) {
        try self.scope.to_free.append(ref);
    }

    if (!slot.borrowed) {
        slot.borrowed = true;
        try self.scope.borrowed.append(ref);
    }

    return ref;
}

fn genVar(self: *Self, variable: Ast.Expr.Var) InnerError!?Scope.Ref {
    var rt_value = (try self.genExpr(variable.init)).?;
    const slot = self.scope.getSlot(rt_value);
    const value = self.types.getValue(variable.init);
    if (value.is_runtime) {
        slot.temorary = false;
    } else {
        rt_value = try self.ensureTemporary(rt_value);
        self.scope.getSlot(rt_value).temorary = false;
    }
    try self.scope.addSymbol(.{ .ref = rt_value });
    return null;
}

fn genRet(self: *Self, ret: Ast.Expr.Id) InnerError!?Scope.Ref {
    const value = (try self.genExpr(ret)).?;
    const loc = self.scope.getSlot(value);
    try self.fb.pushInstr(loc.type, .{ .Mov = .{
        .dst = .{ .Reg = .rax },
        .src = loc.value,
    } });
    try self.fb.pushInstr(Type.usize_lit, .{ .Sub = .{
        .dst = .{ .Reg = .rsp },
        .src = .{ .Imm = self.fb.pushed_stack_size },
    } });
    try self.fb.pushInstrUntyped(.Ret);
    return InnerError.Returned;
}

fn popFrame(
    self: *Self,
    p_frame: Scope.Frame,
    comptime shift_last_slot: bool,
) !if (shift_last_slot) Scope.Ref else void {
    var frame = p_frame;

    for (self.scope.borrowed.items[frame.borrow_len..]) |ref| {
        std.debug.assert(self.scope.getSlot(ref).borrowed);
        self.scope.getSlot(ref).borrowed = false;
    }

    for (self.scope.to_free.items[frame.to_free_len..]) |ref| {
        const slot = self.scope.getSlot(ref);
        if (slot.value != .Reg) continue;
        if (!slot.borrowed) {
            std.debug.print("TODO: {any}\n", .{slot});
            self.regs.free(slot.value.Reg);
            slot.value = .Moved;
            continue;
        }

        self.scope.to_free.items[frame.to_free_len] = ref;
        frame.to_free_len += 1;
    }

    for (0..self.scope.slots.items.len -
        @intFromBool(shift_last_slot) - frame.spill_len) |ri|
    {
        const i = self.scope.slots.items.len - ri - 1 - @intFromBool(shift_last_slot);
        const slot = self.scope.slots.items[i];
        switch (slot.value) {
            .Imm => {},
            .Reg => |r| self.regs.free(r),
            .Stack => |s| if (!s.pushed) {
                //_ = self.fb.freeStack(9);
            },
            .Moved => {},
            .Spilled => |p| {
                const spill = self.scope.getSlot(p.spill);
                std.debug.assert(p.spill.index != i);
                _ = self.fb.popStack(8);
                try self.fb.pushInstr(spill.type, .{ .Pop = .{ .Reg = p.reg } });
                self.regs.restore(p.reg, p.spill);
                spill.value.restore(p.reg);
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
            .Moved => {},
        }
    }

    return new_loc;
}

fn performTest(writer: anytype, comptime name: []const u8, alloc: std.mem.Allocator, src: []const u8) !void {
    var errors = std.ArrayListUnmanaged(Parser.ErrorMessage){};
    defer errors.deinit(alloc);
    var ast = try Parser.parse(alloc, src, &errors);
    defer ast.deinit(alloc);
    for (errors.items) |err| try err.print(writer, src);
    try std.testing.expect(errors.items.len == 0);

    var printer = Ast.Printer(@TypeOf(writer)).init(&ast, writer, src);
    try printer.print();

    var types = try Typechk.check(alloc, &ast, src);
    defer types.deinit(alloc);

    var buffer = std.ArrayList(u8).init(alloc);
    defer buffer.deinit();
    var flout = buffer.writer();

    try flout.writeAll(
        \\    global main
        \\
        \\    section .text
        \\
    );
    try generate(alloc, &ast, &types, src, flout);

    try writer.writeAll(buffer.items);

    const objname = name ++ ".o";
    const filename = name ++ ".asm";
    const executable = name ++ "_test_exe";
    var file = try std.fs.cwd().createFile(filename, .{});
    defer file.close();
    try file.writeAll(buffer.items);

    run(null, &.{ "/usr/bin/nasm", filename, "-felf64", "-o", objname }) catch {};
    run(null, &.{ "/usr/bin/gcc", "-o", executable, objname }) catch {};
    run(writer, &.{"./" ++ executable}) catch {};

    try std.fs.cwd().deleteFile(filename);
    try std.fs.cwd().deleteFile(objname);
    try std.fs.cwd().deleteFile(executable);
}

fn run(writer: anytype, args: []const []const u8) !void {
    var child = std.process.Child.init(args, std.heap.page_allocator);

    if (@TypeOf(writer) == @TypeOf(null)) {
        child.stdout_behavior = .Inherit;
        child.stderr_behavior = .Inherit;
        _ = try child.spawnAndWait();
        return;
    }

    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;
    try child.spawn();

    var stdout = std.ArrayList(u8).init(std.heap.page_allocator);
    var stderr = std.ArrayList(u8).init(std.heap.page_allocator);
    try child.collectOutput(&stdout, &stderr, 100000);
    const term = try child.wait();

    if (term != .Exited or term.Exited != 0) {
        try writer.print("exit code: {any}\n", .{term});

        if (stderr.items.len > 0) {
            try writer.print("stderr:\n{s}\n", .{stderr.items});
        }

        if (stdout.items.len > 0) {
            try writer.print("stdout:\n{s}\n", .{stdout.items});
        }
    }
}

test "print" {
    const tasks = .{
        .{
            "different-integer-sizes",
            \\fn main() u8 {
            \\    return 254 + foo();
            \\}
            \\fn foo() u8 {
            \\    return 2;
            \\}
        },
        .{
            "parens",
            \\fn main() usize {
            \\    return (3 - 2) + 1;
            \\}
        },
        .{
            "parens-2",
            \\fn main() usize {
            \\    return 3 - (2 + 1);
            \\}
        },
        .{
            "fib-iter-recur",
            \\fn main() usize {
            \\    return fib(10, 0, 1);
            \\}
            \\
            \\fn fib(n: usize, a: usize, b: usize) usize {
            \\    if (n == 0) return a;
            \\    return fib(n - 1, b, a + b);
            \\}
        },
        .{
            "fib-recur",
            \\fn main() usize {
            \\    return fib(10);
            \\}
            \\
            \\fn fib(n: usize) usize {
            \\    if (n < 2) return n;
            \\    return fib(n - 1) + fib(n - 2);
            \\}
        },
        .{
            "proper-register-release",
            \\fn main() usize {
            \\    const i = 1 + 2;
            \\    const j = i + 3;
            \\    var k: usize = j;
            \\    k = k + 5 + foo(4);
            \\    var l: usize = j;
            \\    l = l + 5 + foo(4);
            \\    var n: usize = j;
            \\    n = n + 5 + foo(4);
            \\    var m: usize = j;
            \\    m = m + 5 + foo(4);
            \\    var o: usize = j;
            \\    o = o + 5 + foo(4);
            \\    var p: usize = j;
            \\    p = p + 5 + foo(4);
            \\    var q: usize = j;
            \\    q = q + 5 + foo(4);
            \\    var r: usize = j;
            \\    r = r + 5 + foo(4);
            \\    var s: usize = j;
            \\    s = s + 5 + foo(4);
            \\    var t: usize = j;
            \\    t = t + 5 + foo(4);
            \\    var u: usize = j;
            \\    u = u + 5 + foo(4);
            \\    var v: usize = j;
            \\    v = v + 5 + foo(4);
            \\    return k;
            \\}
            \\
            \\fn foo(a: usize) usize {
            \\    return a + a + 4;
            \\}
        },
        .{
            "spilling",
            \\fn main() usize {
            \\    const i = 1 + 2;
            \\    const j = i + 3;
            \\    var k: usize = j;
            \\    k = k + 5 + foo(4);
            \\    var l: usize = j;
            \\    l = l + 5 + foo(4);
            \\    var n: usize = j;
            \\    n = n + 5 + foo(4);
            \\    var m: usize = j;
            \\    m = m + 5 + foo(4);
            \\    var o: usize = j;
            \\    o = o + 5 + foo(4);
            \\    var p: usize = j;
            \\    p = p + 5 + foo(4);
            \\    var q: usize = j;
            \\    q = q + 5 + foo(4);
            \\    var r: usize = j;
            \\    r = r + 5 + foo(4);
            \\    var s: usize = j;
            \\    s = s + 5 + foo(4);
            \\    var t: usize = j;
            \\    t = t + 5 + foo(4);
            \\    var u: usize = j;
            \\    u = u + 5 + foo(4);
            \\    var v: usize = j;
            \\    v = v + 5 + foo(4);
            \\    return k + l - n + m - o + p - q + r - s + t - u + v;
            \\}
            \\
            \\fn foo(a: usize) usize {
            \\    return a + a + 4;
            \\}
        },
        .{
            "simple-if",
            \\fn main() usize {
            \\    return if (false) 1 else if (foo()) 2 else 3;
            \\}
            \\
            \\fn foo() bool {
            \\    return true;
            \\}
        },
        .{
            "if-and-variable",
            \\fn main() usize {
            \\    var a: usize = if (false) 1 else if (foo()) 2 else 3;
            \\    a = a + 1;
            \\    return a;
            \\}
            \\
            \\fn foo() bool {
            \\    return false;
            \\}
        },
    };

    var failed = false;
    inline for (tasks) |task| {
        std.debug.print("running test: {s}\n", .{task[0]});
        //if (comptime !std.mem.eql(u8, task[0], "spilling")) continue;
        garbage.printtest(task[0], performTest, task[1]) catch |err| switch (err) {
            error.DiffFailed => failed = true,
            else => |e| return e,
        };
    }

    if (failed) std.log.err("some tests failed", .{});
}
