const std = @import("std");
const maxIdentLen = @import("Ident.zig").cap;
const garbage = @import("garbage.zig");

const Self = @This();
pub const Token = enum {
    Ident,
    Underscore,
    Number,

    Add,
    Sub,
    Assign,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,

    Colon,
    Semi,
    Comma,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,

    KeyVar,
    KeyConst,
    KeyIf,
    KeyElse,
    KeyReturn,
    KeyFn,
    KeyUsize,
    KeyIsize,
    KeyBool,
    KeyVoid,
    KeyTrue,
    KeyFalse,

    Int,
    Uint,

    TooLongIdent,
    Unknown,
    Eof,

    pub fn dispatchKeyword(str: []const u8) ?Token {
        comptime var first_keyword: ?usize = null;
        const keyword_names = comptime b: {
            const prefix = "Key";
            const data = @typeInfo(Token).Enum;

            var count = 0;
            for (data.fields) |value| {
                if (value.name.len > prefix.len and std.mem.eql(u8, value.name[0..prefix.len], prefix)) {
                    count += 1;
                }
            }

            var keyword_names: [count][]const u8 = undefined;
            for (data.fields, 0..) |value, i| {
                if (value.name.len > prefix.len and std.mem.eql(u8, value.name[0..prefix.len], prefix)) {
                    if (first_keyword == null) {
                        first_keyword = i;
                    }
                    keyword_names[i - first_keyword.?] = garbage.toLowerCt(value.name[prefix.len..]);
                }
            }

            break :b keyword_names;
        };

        const Lookup = Self.KeywordLookup(&keyword_names, &.{
            &.{ .{ 2, 6 }, .{ 'i', 'i' }, .{ '1', '9' }, .{ '0', '9' }, .{ '0', '9' }, .{ '0', '9' } },
            &.{ .{ 2, 6 }, .{ 'u', 'u' }, .{ '1', '9' }, .{ '0', '9' }, .{ '0', '9' }, .{ '0', '9' } },
        });

        const index = Lookup.lookup(str);
        if (index) |i| return @enumFromInt(i + first_keyword.?);
        return null;
    }
};

pub const TokenMeta = struct {
    kind: Token,
    pos: usize,
    source: []const u8,
};

source: []const u8,
cursor: usize,

pub fn init(source: []const u8) Self {
    return Self{ .source = source, .cursor = 0 };
}

pub fn nextToken(self: *Self) TokenMeta {
    while (self.cursor < self.source.len) {
        const pos = self.cursor;
        var c = self.advance();
        const kind = switch (c) {
            ' ', '\t', '\n', '\r' => continue,

            'a'...'z', 'A'...'Z', '_' => b: {
                while (self.cursor < self.source.len) {
                    switch (self.source[self.cursor]) {
                        'a'...'z', 'A'...'Z', '_', '0'...'9' => _ = self.advance(),
                        else => break,
                    }
                }

                if (self.source[pos] == '_' and self.cursor - pos == 1) {
                    break :b .Underscore;
                }

                if (self.cursor - pos > maxIdentLen) {
                    break :b .TooLongIdent;
                }

                break :b Token.dispatchKeyword(self.source[pos..self.cursor]) orelse .Ident;
            },
            '0'...'9' => b: {
                while (self.cursor < self.source.len) {
                    switch (self.source[self.cursor]) {
                        '0'...'9' => _ = self.advance(),
                        else => break,
                    }
                }
                break :b .Number;
            },

            ':' => .Colon,
            ';' => .Semi,
            ',' => .Comma,

            '+' => .Add,
            '-' => .Sub,
            '=' => if (self.tryAdvance('=') != null) Token.Eq else .Assign,
            '<' => if (self.tryAdvance('=') != null) Token.Le else .Lt,
            '>' => if (self.tryAdvance('=') != null) Token.Ge else .Gt,
            '!' => if (self.tryAdvance('=') != null) Token.Ne else .Unknown,

            '(' => .LParen,
            ')' => .RParen,
            '{' => .LBrace,
            '}' => .RBrace,
            '[' => .LBrack,
            ']' => .RBrack,

            else => .Unknown,
        };

        return TokenMeta{ .kind = kind, .pos = pos, .source = self.source[pos..self.cursor] };
    }

    return TokenMeta{ .kind = .Eof, .pos = self.cursor, .source = "" };
}

fn tryAdvance(self: *Self, c: u8) ?u8 {
    if (self.cursor < self.source.len and self.source[self.cursor] == c) {
        defer self.cursor += 1;
        return c;
    }
    return null;
}

fn advance(self: *Self) u8 {
    defer self.cursor += 1;
    return self.source[self.cursor];
}

fn KeywordLookup(comptime keywords: []const []const u8, comptime patterns: []const []const [2]u8) type {
    @setEvalBranchQuota(10000);

    for (keywords) |keyword| std.debug.assert(keyword.len > 0);

    var max_len = 0;
    for (keywords) |keyword| {
        max_len = @max(max_len, keyword.len);
    }

    var min_len = max_len;
    for (keywords) |keyword| {
        min_len = @min(min_len, keyword.len);
    }

    for (patterns) |pattern| {
        min_len = @min(min_len, pattern[0][0]);
        max_len = @max(max_len, pattern[0][1]);
    }

    const KeywordMask = std.meta.Int(.unsigned, std.math.ceilPowerOfTwo(u16, keywords.len + patterns.len) catch unreachable);
    const char_count = 127;

    var table_init: [char_count][max_len]KeywordMask = undefined;
    for (&table_init) |*row| for (row) |*cell| {
        cell.* = 0;
    };
    for (keywords, 0..) |keyword, k| for (keyword, 0..) |kc, i| {
        const index = kc;
        table_init[index][i] |= @as(KeywordMask, 1) << k;
    };
    for (patterns, keywords.len..) |pattern, k| for (pattern[1..], 0..) |pc, i| {
        for (pc[0]..pc[1] + 1) |c| {
            table_init[c][i] |= @as(KeywordMask, 1) << k;
        }
    };

    var len_table_init: [max_len - min_len + 1]KeywordMask = undefined;
    for (&len_table_init) |*row| row.* = 0;
    for (keywords, 0..) |keyword, i| len_table_init[keyword.len - min_len] |= @as(KeywordMask, 1) << i;
    for (patterns, keywords.len..) |pattern, i| for (pattern[0][0]..pattern[0][1] + 1) |j| {
        len_table_init[j - min_len] |= @as(KeywordMask, 1) << i;
    };

    const table_init_final = table_init;
    const len_table_final = len_table_init;
    const min_len_final = min_len;
    const max_len_final = max_len;

    return struct {
        const table = table_init_final;
        const len_table = len_table_final;

        pub fn lookup(str: []const u8) ?usize {
            if (str.len < min_len_final or str.len > max_len_final) {
                return null;
            }

            var mask = len_table[str.len - min_len_final];
            for (str, 0..) |c, i| {
                mask &= table[c][i];
            }

            if (mask == 0) {
                return null;
            }

            return @ctz(mask);
        }
    };
}

test {
    std.testing.refAllDeclsRecursive(Self);
}

test "keyword" {
    try std.testing.expectEqual(Token.KeyVar, Token.dispatchKeyword("var").?);
    try std.testing.expectEqual(@as(?Token, null), Token.dispatchKeyword("fl"));
}

test "sanity" {
    const source =
        \\ abc l suba _mach3 u333
        \\ let fn ret
        \\ 123 456 789
        \\ + - =
        \\ : ; ,
        \\ ( ) { } [ ]
    ;

    const expected = [_][]const u8{
        "abc", "l",  "suba", "_mach3", "u333",
        "let", "fn", "ret",  "123",    "456",
        "789", "+",  "-",    "=",      ":",
        ";",   ",",  "(",    ")",      "{",
        "}",   "[",  "]",
    };

    var lexer = Self.init(source);

    for (expected) |ex| {
        const token = lexer.nextToken();
        try std.testing.expectEqualStrings(ex, token.source);
    }
}
