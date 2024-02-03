const std = @import("std");
const Ast = @import("Ast.zig");

const Scope = @This();

pub const Frame = struct {
    sym_count: usize = 0,
    ordered_sym_count: usize = 0,
};

pub const Sym = struct {
    ident: Ast.Ident,
    resolved: bool,
    used: bool = false,
    last_occurence: Occurence,
};

pub const Occurence = union(enum) {
    Expr: Ast.Expr.Id,
    Item,
    Param,
    Var,
};

symbols: std.ArrayList(Sym),
item_count: usize = 0,
ordered_sym_count: usize = 0,
peak_ordered_sym_count: usize = 0,

pub fn init(alloc: std.mem.Allocator) Scope {
    return .{ .symbols = std.ArrayList(Sym).init(alloc) };
}

pub fn deinit(self: *Scope) void {
    self.symbols.deinit();
}

pub fn pushFrame(self: *Scope) Frame {
    return .{
        .sym_count = self.symbols.items.len,
        .ordered_sym_count = self.ordered_sym_count,
    };
}

pub fn popFrame(self: *Scope, frame: Frame) void {
    var to_keep = frame.sym_count;
    for (frame.sym_count..self.symbols.items.len) |i| {
        const sym = self.symbols.items[i];
        if (!sym.resolved) {
            self.symbols.items[to_keep] = sym;
            to_keep += 1;
        }
    }

    self.peak_ordered_sym_count = @max(self.peak_ordered_sym_count, self.ordered_sym_count);

    self.symbols.items.len = to_keep;
    self.ordered_sym_count = frame.ordered_sym_count;
}

pub fn add(self: *Scope, loc: Occurence, ident: []const u8, source: []const u8) !Ast.Ident {
    return self.handleSym(loc, ident, source, true);
}

pub fn dispatch(self: *Scope, loc: Occurence, ident: []const u8, source: []const u8) !Ast.Ident {
    return self.handleSym(loc, ident, source, false);
}

fn handleSym(
    self: *Scope,
    loc: Occurence,
    ident: []const u8,
    source: []const u8,
    declare: bool,
) !Ast.Ident {
    for (0..self.symbols.items.len) |ri| {
        const i = self.symbols.items.len - ri - 1;
        const sym = &self.symbols.items[i];
        if (sym.ident.len != ident.len) continue;
        if (std.mem.eql(u8, sym.ident.slice(source), ident)) {
            if (sym.resolved and declare) return error.DuplicateSymbol;
            sym.resolved = sym.resolved or declare;
            if (!sym.ident.unordered or declare) sym.last_occurence = loc;
            sym.used = true;
            return sym.ident;
        }
    }

    const pos = @intFromPtr(ident.ptr) - @intFromPtr(source.ptr);
    const index = switch (loc) {
        .Item, .Expr => self.item_count,
        else => self.ordered_sym_count,
    };
    const sym = Ast.Ident.init(pos, ident.len, index, loc == .Expr or loc == .Item);
    try self.symbols.append(.{
        .ident = sym,
        .resolved = declare,
        .last_occurence = loc,
    });

    switch (loc) {
        .Item, .Expr => self.item_count += 1,
        else => self.ordered_sym_count += 1,
    }

    return sym;
}
