const std = @import("std");
const allocer = std.heap.c_allocator;
pub fn assert (condition:bool, comptime message:[]const u8, args:anytype) void {
    if (!condition) {
        std.debug.print("\n-----------------------\nAssertion failed: " ++ message ++ "\n-----------------------\nTrace:\n", args);
        unreachable;
    }
}
const debugLog = std.debug.print;

const Tuple = std.meta.Tuple;

const Token = struct {
    char:u8,
    kind:Kind,

    pub const Kind = enum {
        Char,
        AnyChar,
        Concat,
        Union,
        Kleen,
        LParen,
        RParen,

        // hope that the compiler knows that this is often used at comptime
        pub fn precedenceAndChar(self:@This()) struct{prec:u8, char:u8} {
            return switch(self){
                Kind.Char    => .{.prec = 0, .char = 'x'},
                Kind.AnyChar => .{.prec = 0, .char = '.'},
                Kind.Union   => .{.prec = 1, .char = '|'},
                Kind.Concat  => .{.prec = 2, .char = ' '},
                Kind.Kleen   => .{.prec = 3, .char = '*'},
                Kind.LParen  => .{.prec = 0, .char = '('},
                Kind.RParen  => .{.prec = 0, .char = ')'},
            };
        }

        pub fn fromChar(theChar:u8) @This() {
            // this seems to get compiled into smth proper
            return switch(theChar){
                Kind.AnyChar.precedenceAndChar().char => Kind.AnyChar,
                Kind.Union.precedenceAndChar().char   => Kind.Union,
                Kind.Kleen.precedenceAndChar().char   => Kind.Kleen,
                Kind.LParen.precedenceAndChar().char  => Kind.LParen,
                Kind.RParen.precedenceAndChar().char  => Kind.RParen,
                else                                  => Kind.Char
            };
        }

        pub fn canConcatToRight(self:@This()) bool {
            return switch(self){
                Kind.Char    => true,
                Kind.AnyChar => true,
                Kind.Kleen   => true,
                Kind.RParen  => true,
                else         => false
            };
        }
        pub fn canConcatToLeft(self:@This()) bool {
            return switch(self){
                Kind.Char    => true,
                Kind.AnyChar => true,
                Kind.LParen  => true,
                else         => false
            };
        }
    };

    pub fn initChar(char:u8) @This() {
        return Token{
            .kind = Token.Kind.fromChar(char),
            .char = char
        };
    }

    pub fn initKind(kind:Kind) @This() {
        return Token{
            .kind = kind,
            .char = kind.precedenceAndChar().char
        };
    }
};

fn tokenize(input:[]const u8) error{OutOfMemory}![]Token {
    // we need to fill in concat tokens, as they are implicit in the input
    var tokens:[]Token = try allocer.alloc(Token, input.len << 1); // multiply by 2 to account for concat tokens
    var i:u32 = 0;
    for (input) |char| {
        const curToken = Token.initChar(char);
        // hope this gets unrolled
        if(i > 0 and curToken.kind.canConcatToLeft() and tokens[i-1].kind.canConcatToRight()) {
            tokens[i] = Token.initKind(Token.Kind.Concat);
            i+=1;
            tokens[i] = curToken;
        }else{
            tokens[i] = curToken;
        }
        i+=1;
    }
    return try allocer.realloc(tokens, i);
}

const SyntaxError = error{InvalidToken};
const ParseError = error{InvalidToken, OutOfMemory};

const Tokenizer = struct {
    tokens:[]Token,
    cur:u32,

    pub fn init(input:[]const u8) !@This() {
        const tokens = try tokenize(input);
        return Tokenizer{
            .tokens = tokens,
            .cur = 0,
        };
    }

    pub fn peek(self:*const Tokenizer) Token {
        return self.tokens[self.cur];
    }

    pub fn next(self:*Tokenizer) Token {
        const tok = self.tokens[self.cur];
        self.cur += 1;
        return tok;
    }

    pub fn hasNext(self:*const Tokenizer) bool {
        return self.cur < self.tokens.len;
    }
    
    pub fn matchNext(self:*Tokenizer, kind:Token.Kind, comptime advance:bool) bool {
        if(self.hasNext() and self.peek().kind == kind) {
            if (advance)
                self.cur += 1;
            return true;
        }
        return false;
    }

    pub fn assertNext(self:*Tokenizer, kind:Token.Kind) SyntaxError!void {
        if(!self.matchNext(kind, true)) {
            return SyntaxError.InvalidToken;
        }
    }

    pub fn deinit(self:@This()) void {
        allocer.free(self.tokens);
    }

    fn debugFmt(self:@This()) !std.ArrayList(u8) {
        var buf = try std.ArrayList(u8).initCapacity(allocer, self.tokens.len);
        const writer = buf.writer();
        for (self.tokens) |tok| {
            try writer.print("{?c}", .{tok.char});
        }
        return buf;
    }
};

const RegEx = struct {
    left:?*const RegEx,
    right:?*const RegEx,
    kind:Token.Kind,
    char:u8,

    pub fn initLiteralChar(char:u8) @This() {
        return RegEx{
            .left = null,
            .right = null,
            .kind = Token.Kind.Char,
            .char = char,
        };
    }

    pub fn initOperator(kind:Token.Kind, left:*const RegEx, right:?*const RegEx) @This() {
        return RegEx{
            .left = left,
            .right = right,
            .kind = kind,
            .char = kind.precedenceAndChar().char,
        };
    }

    pub fn parsePrimaryExpr(tok:*Tokenizer) ParseError!*@This() {
        var primary:*RegEx = undefined;
        if(tok.matchNext(Token.Kind.LParen, true)) {
            primary = try parseExpr(0, tok);
            try tok.assertNext(Token.Kind.RParen);
        }else{
            primary = try allocer.create(RegEx);
            primary.* = initLiteralChar(tok.next().char);
        }

        if(tok.matchNext(Token.Kind.Kleen, true)) { // kleens prec is ignored because its the highest anyway
            var kleen = try allocer.create(RegEx);
            kleen.* = initOperator(Token.Kind.Kleen, primary, null);
            return kleen;
        }
        return primary;
    }

    pub fn parseExpr(minPrec:u32, tok:*Tokenizer) ParseError!*@This() {
        var lhs = try parsePrimaryExpr(tok);
        while (tok.hasNext()) {
            debugLog("lhs: {c}, minPrec: {d}, next token: {c}\n", .{lhs.char, minPrec, tok.peek().char});
            // let the upper level parse 'unknown operators' (in this case anything but the binary operators)
            var operatorKind = tok.peek().kind; // we peek, because if we return inside the loop, the upper level needs to consume that token
            assert(operatorKind != Token.Kind.Char and operatorKind != Token.Kind.AnyChar, "unexpected token: {c}", .{operatorKind.precedenceAndChar().char});
            if(operatorKind != Token.Kind.Union and operatorKind != Token.Kind.Concat)
                return lhs;

            var prec = operatorKind.precedenceAndChar().prec;
            if (prec < minPrec)
                return lhs;

            _ = tok.next(); // consume operator



            var rhs = try parseExpr(prec + 1, tok); // always + 1, because we only have left-associative operators, so we want to bind the same operator again in the next depth, not in the one above
            var op = try allocer.create(RegEx);
            op.* = initOperator(operatorKind, lhs, rhs);
            lhs = op;
        }
        return lhs;
    }

    fn printDOTInternal(self:RegEx, writer:anytype, num:u128) !void {
        // depth above 127 is undefined for now
        try writer.print("n{}[label=\"{?c}\"];", .{num,self.char});
        if (self.left) |left| {
            try writer.print("n{} -> n{};",   .{num,     num << 1});
            try left.printDOTInternal(writer, num << 1);
        }
        if (self.right) |right| {
            try writer.print("n{} -> n{};",    .{num,           (num << 1) + 1});
            try right.printDOTInternal(writer, (num << 1) + 1);
        }
    }

    pub fn printDOTRoot(self:RegEx, writer:anytype) !void {
        try writer.print("digraph RegEx {{", .{});
        try self.printDOTInternal(writer, 1);
        try writer.print("}}\n", .{});
    }
};

const RegExDFA = struct{
    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    // an insert-first-lookup-later sorted vector like map would be preferable here for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends), but this will do for now
    transitions:[]std.AutoHashMap(u8, u32),
    finalStates:std.AutoHashMap(u32,void), // saw this online, but i kinda doubt there is a good specialization for void...
                                           // a sorted vector would again be better

    pub fn init() !@This() {
        return RegExDFA{
            .startState  = 0,
            .numStates   = 0,
            .transitions = try allocer.alloc(std.AutoHashMap(u8, u32), 0),
            .finalStates = std.AutoHashMap(u32, void).init(allocer)
        };
    }

    pub fn addState(self:*@This()) !u32{
        try self.addStates(1);
        return self.numStates - 1;
    }

    pub fn addStates(self:*@This(), comptime n:comptime_int) !void{
        self.numStates += n;
        self.transitions = try allocer.realloc(self.transitions, self.numStates);
        for(self.numStates-n..self.numStates) |i| {
            self.transitions[i] = std.AutoHashMap(u8, u32).init(allocer);
        }
    }

    pub fn designateStatesFinal(self:*@This(), states:[]const u32) !void{
        for (states) |state| {
            try self.finalStates.put(state, {});
        }
    }


    pub fn isInLanguage(self:@This(), word:[]const u8) bool{
        var curState:u32 = self.startState;
        for(word) |c| {
            curState = self.transitions[curState].get(c) orelse return false;
        }
        return self.finalStates.contains(curState);
    }
};

const RegExNFA = struct {
    const TransitionsOfAState = std.AutoHashMap(?u8, std.ArrayList(u32));
    const FinalStates = std.AutoHashMap(u32,void);

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    // an insert-first-lookup-later sorted vector like map would be preferable here for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends), but this will do for now
    transitions:[]TransitionsOfAState, // ?u8 for eps transitions
    finalStates:FinalStates, // saw this online, but i kinda doubt there is a good specialization for void...

    pub fn init() !@This() {
        return RegExNFA{
            .startState  = 0,
            .numStates   = 0,
            .transitions = try allocer.alloc(TransitionsOfAState, 0),
            .finalStates = FinalStates.init(allocer)
        };
    }

    pub fn addState(self:*@This()) !u32{
        try self.addStates(1);
        return self.numStates - 1;
    }

    pub fn addStates(self:*@This(), comptime n:comptime_int) !void{
        self.numStates += n;
        self.transitions = try allocer.realloc(self.transitions, self.numStates);
        for(self.numStates-n..self.numStates) |i| {
            self.transitions[i] = TransitionsOfAState.init(allocer);
        }
    }

    pub fn addTransition(self:*@This(), from:u32, with:?u8, to:u32) !void {
        var entry = try self.transitions[from].getOrPut(with);
        if(!entry.found_existing)
            entry.value_ptr.* = std.ArrayList(u32).init(allocer);

        try entry.value_ptr.append(to);
    }

    pub fn designateStatesFinal(self:*@This(), states:[]const u32) !void{
        for (states) |state| {
            try self.finalStates.put(state, {});
        }
    }

    pub fn addAllTransitionsFromOtherState(self:*@This(), transitionToCopyTo:*TransitionsOfAState, stateToCopyFrom:u32) !void{
        // there doesn't seem to be a 'put all', so I guess we'll loop...
        var it = self.transitions[stateToCopyFrom].iterator();
        while(it.next()) |transition| {
            var entry = try transitionToCopyTo.getOrPut(transition.key_ptr.*);
            if (!entry.found_existing) {
                entry.value_ptr.* = try transition.value_ptr.clone();
            }else{
                try entry.value_ptr.*.appendSlice(transition.value_ptr.*.items);
            }
        }
    }

    // does not eliminate, but 'fill' epsilon transitions, so that they can be ignored from now on (because the language of the NFA after this function is the same with or without them)
    pub fn backUpEpsTransitions(self:*@This()) !void {
        for(0.., self.transitions) |state,*transitionsFromState| {
            if(transitionsFromState.get(null)) |epsTransitionsFromState| {
                // solution: copy all transitions of the targeted states (epsTransitionTargetsFromState) to the current state
                // also if the target is a final state, make this one final too
                for(epsTransitionsFromState.items) |epsTargetState|{
                    try self.addAllTransitionsFromOtherState(transitionsFromState, epsTargetState);

                    // make final if target is final
                    if(self.finalStates.contains(epsTargetState))
                        try self.designateStatesFinal(&[1]u32{@truncate(state)});
                }
            }
        }
    }

    // this function assumes backUpEpsTransitions has been called before!
    //pub fn powersetConstruction(self:*@This()) !void{
        // TODO
    //}
};

// TODO (eps-)NFA, removing eps transitions, powerset construction, then we can simply construct the eps-NFA from the regex and then convert it to a DFA

const expect = std.testing.expect;

test "tokenizer" {
    const input = "xyz|w*(abc)*de*f";
    var tok = try Tokenizer.init(input);
    defer tok.deinit();
    const buf = try tok.debugFmt();
    try expect(std.mem.eql(u8, buf.items, "x y z|w* (a b c)* d e* f"));
}

test "ab* DFA" {
    var dfa = try RegExDFA.init();
    try dfa.addStates(2);
    const a = 0;
    const b = 1;

    try dfa.transitions[a].put('a', b);
    try dfa.transitions[b].put('b', b);
    try dfa.designateStatesFinal(&[1]u32{b});

    try expect(dfa.isInLanguage("a"));
    try expect(dfa.isInLanguage("ab"));
    try expect(dfa.isInLanguage("abb"));
    try expect(dfa.isInLanguage("abbbbbbbbbbbbbbbbbbbbbbbbbb"));
    try expect(!dfa.isInLanguage("b"));
    try expect(!dfa.isInLanguage("ba"));
    try expect(!dfa.isInLanguage("aba"));
    try expect(!dfa.isInLanguage("abbbbbbbbbbbbbbbbbbbbbbbbbba"));
}

test "ab|aaa NFA" {
    var nfa = try RegExNFA.init();
    try nfa.addStates(6);
    try nfa.addTransition(0, 'a', 1);
    try nfa.addTransition(0, 'a', 2);
    try nfa.addTransition(1, 'b', 3);
    try nfa.addTransition(2, 'a', 4);
    try nfa.addTransition(4, 'a', 5);
    try nfa.designateStatesFinal(&[_]u32{3,5});
}

test "NFA eps removal" {
    var nfa = try RegExNFA.init();
    try nfa.addStates(2);
    try nfa.addTransition(0, null, 1);
    try nfa.addTransition(1, 'a', 1);
    try nfa.designateStatesFinal(&[_]u32{1});

    try expect(!nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].get('a') == null);

    try nfa.backUpEpsTransitions();

    try expect(nfa.finalStates.contains(0));
    try expect((nfa.transitions[0].get('a') orelse unreachable).items[0] == 1);
}

pub fn main() !void {
    const writer = std.io.getStdOut().writer();
    //const a = RegEx.initLiteralChar('a');
    //const b = RegEx.initLiteralChar('b');
    //
    //const aOrB = RegEx.initOperator(Token.Kind.Union, &a, &b);
    //try aOrB.printDOTRoot(writer);

    const input = "xyz|w*(abc)*de*f";
    //const input = "xyz";

    var tok = try Tokenizer.init(input);
    defer tok.deinit();
    const regex = try RegEx.parseExpr(0, &tok);
    assert(!tok.hasNext(), "expected EOF, but there were tokens left", .{});
    try regex.printDOTRoot(writer);
}
