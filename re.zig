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

fn initArrayListLikeWithElements(allocator:std.mem.Allocator, comptime ArrayListType:type, elementsSlice:anytype) !ArrayListType{
    var arrayListLike = try ArrayListType.initCapacity(allocator, elementsSlice.len);
    errdefer arrayListLike.deinit();

    try arrayListLike.appendSlice(elementsSlice);

    return arrayListLike;
}

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

// (eps-)NFA, removing eps transitions, powerset construction, then we can simply construct the eps-NFA from the regex and then convert it to a DFA to perform checks
// TODO constructing the eps-NFA from a regex is the only thing left to do

const RegExDFA = struct{
    const TransitionsOfAState = std.AutoHashMap(u8, u32);

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    // an insert-first-lookup-later sorted vector like map would be preferable here for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends), but this will do for now
    transitions:[]TransitionsOfAState,
    finalStates:std.AutoHashMap(u32,void), // saw this online, but i kinda doubt there is a good specialization for void...
                                           // a sorted vector would again be better

    pub fn init() !@This() {
        return RegExDFA{
            .startState  = 0,
            .numStates   = 0,
            .transitions = try allocer.alloc(TransitionsOfAState, 0),
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
            self.transitions[i] = TransitionsOfAState.init(allocer);
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

// TODO make sure that this doesn't work by copying -> do i need pointers here? would that still work?
const FiniteAutomaton = union(enum){
    dfa:RegExDFA,
    nfa:RegExNFA,

    pub fn printDOT(self:FiniteAutomaton, writer:anytype) !void {
        try writer.print("digraph FiniteAutomaton {{ node[shape=circle];", .{});

        const startState = switch(self){
            inline else => |case| case.startState
        };

        const states = switch(self){
            inline else => |case| case.numStates
        };

        const finalStates = switch(self){
            inline else => |case| case.finalStates
        };

        var curState = startState;
        for(0..states) |_| {
            try writer.print("n{}[label=\"{}\"", .{curState, curState});
            if(finalStates.contains(curState)){
                try writer.print(",shape=doublecircle", .{});
            }
            try writer.print("]; ", .{});

            switch(self){
                FiniteAutomaton.dfa => |dfa| {
                    var it = dfa.transitions[curState].iterator();
                    while(it.next()) |transition| {
                        try writer.print("n{} -> n{}[label=\"{c}\"]; ", .{curState, transition.value_ptr.*, transition.key_ptr.*});
                    }
                },
                FiniteAutomaton.nfa => |nfa| {
                    var it = nfa.transitions[curState].iterator();
                    // could also put the same transitions on the same edge, reduce clutter a bit, but this is only for debugging anyway
                    while(it.next()) |transitions| {
                        for(transitions.value_ptr.items) |targetState| {
                            if(transitions.key_ptr.*) |c| {
                                try writer.print("n{} -> n{}[label=\"{c}\"]; ", .{curState, targetState, c});
                            }else{
                                try writer.print("n{} -> n{}[label=\"&epsilon;\"]; ", .{curState, targetState});
                            }
                        }
                    }
                },
            }

            curState += 1;
        }

        // for start state
        try writer.print("n{}[label=\"\",style=\"invis\"];n{} -> n{}; ", .{curState, curState, startState});

        try writer.print("}}\n", .{});
    }
};

const RegExNFA = struct {
    // an insert-first-lookup-later sorted vector like map would be preferable here for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends), but this will do for now
    const TransitionsOfAState = std.AutoHashMap(?u8, std.ArrayList(u32)); // ?u8 for eps transitions
    const FinalStates = std.AutoHashMap(u32,void);// saw this online, but i kinda doubt there is a good specialization for void...

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    transitions:[]TransitionsOfAState,
    finalStates:FinalStates, 

    internalArena:std.heap.ArenaAllocator,
    internalAllocator:std.mem.Allocator,

    pub fn init() !@This() {
        var nfa                = RegExNFA{
            .startState        = 0,
            .numStates         = 0,
            .transitions       = undefined,
            .finalStates       = undefined,
            .internalArena     = std.heap.ArenaAllocator.init(allocer),
            .internalAllocator = undefined,
        };
        // TODO panics for some reason (doesnt seem to be a recoverable Error), so im just using the allocer again for now. That will leak like crazy, so this definitely needs to be fixed
        //nfa.internalAllocator = nfa.internalArena.allocator();
        nfa.internalAllocator = allocer;
        nfa.transitions       = try nfa.internalAllocator.alloc(TransitionsOfAState, 0);
        nfa.finalStates       = FinalStates.init(nfa.internalAllocator);
        return nfa;
    }

    pub fn addState(self:*@This()) !u32{
        try self.addStates(1);
        return self.numStates - 1;
    }

    pub fn addStates(self:*@This(), comptime n:comptime_int) !void{
        self.numStates += n;
        self.transitions = try self.internalAllocator.realloc(self.transitions, self.numStates);
        for(self.numStates-n..self.numStates) |i| {
            self.transitions[i] = TransitionsOfAState.init(self.internalAllocator);
        }
    }

    pub fn addTransition(self:*@This(), from:u32, with:?u8, to:u32) !void {
        var entry = try self.transitions[from].getOrPut(with);
        if(!entry.found_existing)
            entry.value_ptr.* = try std.ArrayList(u32).initCapacity(self.internalAllocator, 1);

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

    // this function assumes backUpEpsTransitions has been called just before!
    // this also deinitializes the NFA, so it can't be used afterwards
    // TODO handle different allocator for DFA, currently that just does malloc
    pub fn toPowersetConstructedDFA(self:*@This()) !RegExDFA{
        // combine all transitions into new states (if they don't exist yet), add them to the worklist

        // maps input array list of nfa states to dfa state
        var nfaToDfaStates = std.HashMap([]u32, u32, struct {
            // just a simple hashing of slice *content*
            pub fn hash(_: @This(), key: []u32) u64 {
                var h = std.hash.Wyhash.init(0);
                for(key) |state| {
                    h.update(std.mem.asBytes(&state));
                }
                return h.final();
            }

            pub fn eql(_: @This(), a: []u32, b: []u32) bool {
                return std.mem.eql(u32, a, b);
            }
        }, std.hash_map.default_max_load_percentage).init(self.internalAllocator);
        
        var dfa = try RegExDFA.init();
        // worklist of nfa (and generated i.e. powerset-) states to visit
        var worklist = try std.ArrayList(std.ArrayList(u32)).initCapacity(self.internalAllocator, 8);

        // add start state to new DFA
        dfa.startState = try dfa.addState();
        var startStateList = try initArrayListLikeWithElements(self.internalAllocator, std.ArrayList(u32), &[1]u32{self.startState});
        try nfaToDfaStates.putNoClobber(startStateList.items, dfa.startState);

        // used like a stack
        try worklist.append(startStateList);


        // TODO 'curNfaState(s)' is not named perfectly, because it can also be a 'powerset state' that doesnt exist in the original NFA, just implicitly
        while(worklist.popOrNull()) |curNfaStates| {
            // get the state, has to be in there (but not visited yet) if its in the worklist
            const curDfaState = nfaToDfaStates.get(curNfaStates.items) orelse unreachable;

            // if any of the current nfa states is final, make the dfa state final
            loop: for(curNfaStates.items) |curNfaState| {
                if(self.finalStates.contains(curNfaState)){
                    try dfa.designateStatesFinal(&[1]u32{@truncate(curDfaState)});
                    break :loop;
                }
            }

            // then go through the transitions of the states, and construct a transition map for the state step by step
            // after the transition map is complete, the actual dfa states can be created and the dfa transitions can be added
            var combinedTransitionsForCurNfaState = std.AutoHashMap(u8, std.ArrayList(u32)).init(self.internalAllocator);
            // the transition lists in here are kept sorted, for deduplication (as they represent sets)

            for(curNfaStates.items) |curNfaState| {
                var it = self.transitions[curNfaState].iterator();

                while(it.next()) |transition| {
                    // ignore empty, because eps transitions are already handled
                    if(transition.key_ptr.*) |c| {
                        var entry = try combinedTransitionsForCurNfaState.getOrPut(c);
                        // either create or append (keep sorted)
                        if(!entry.found_existing){
                            entry.value_ptr.* = try transition.value_ptr.clone();
                            std.sort.pdq(u32, entry.value_ptr.items, {}, std.sort.asc(u32));
                        }else{
                            // add all targets of the transition to the combined state set, but only if they are not already in there
                            targetStateLoop: for(transition.value_ptr.items) |targetState| {
                                // binary search, but we can't use the std.sort one, because we need to insert if not found
                                // so just copy that one and change it :)
                                var left: usize = 0;
                                var right: usize = entry.value_ptr.items.len;

                                while (left < right) {
                                    // Avoid overflowing in the midpoint calculation
                                    const mid = left + (right - left) / 2;
                                    // Compare the key with the midpoint element
                                    if(targetState < entry.value_ptr.items[mid]){
                                        right = mid;
                                    }else if(targetState > entry.value_ptr.items[mid]){
                                        left = mid + 1;
                                    }else{
                                        // go to next, the state already exists in the combined state set
                                        continue :targetStateLoop;
                                    }
                                }

                                // if it didn't find anything, the next bigger value is at index left=right
                                assert(left == right, "binary search behaved weirdly", .{});

                                // so insert right before there
                                try entry.value_ptr.insert(left, targetState);
                            }
                        }
                    }
                }
            }

            // now we have the combined transitions for the current state, so we can create the actual states and add the transitions in the dfa

            var it = combinedTransitionsForCurNfaState.iterator();
            while(it.next()) |transition| {
                // create or get state
                var targetStateEntry = try nfaToDfaStates.getOrPut(transition.value_ptr.*.items);
                if(!targetStateEntry.found_existing){
                    targetStateEntry.value_ptr.* = try dfa.addState();

                    // add (the possibly combined state of the nfa) to worklist, because its new -> we haven't visited it yet
                    try worklist.append(transition.value_ptr.*);
                }

                // add transition
                try dfa.transitions[curDfaState].putNoClobber(transition.key_ptr.*, targetStateEntry.value_ptr.*);
            }

        }

        // TODO when the arena allocator works call deinit etc.

        return dfa;
    }
};

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

test "NFA simple powerset construction" {
    var nfa = try RegExNFA.init();
    try nfa.addStates(6);
    try nfa.addTransition(0, 'a', 1);
    try nfa.addTransition(0, 'a', 2);
    try nfa.addTransition(1, 'b', 3);
    try nfa.addTransition(2, 'a', 4);
    try nfa.addTransition(4, 'a', 5);
    try nfa.designateStatesFinal(&[_]u32{3,5});

    var dfa = try nfa.toPowersetConstructedDFA();
    try expect(dfa.isInLanguage("ab"));
    try expect(dfa.isInLanguage("aaa"));

    // nothing else should be in the language
    // lets just test a bunch of random strings

    var rnd = std.rand.DefaultPrng.init(0);
    for(0..10000) |_| {
        var length = rnd.random().int(u8);
        var buf = try std.testing.allocator.allocSentinel(u8, length, 0);
        defer std.testing.allocator.free(buf);
        for(buf) |*c| {
            c.* = rnd.random().int(u8);
        }
        try expect(!dfa.isInLanguage(buf));
    }
}

test "complex eps-NFA powerset construction" {
    var nfa = try RegExNFA.init();
    try nfa.addStates(4);
    try nfa.addTransition(0, null, 2);
    try nfa.addTransition(0, 'a', 1);
    try nfa.addTransition(1, 'b', 1);
    try nfa.addTransition(2, 'c', 1);
    try nfa.addTransition(2, 'd', 3);
    try nfa.addTransition(2, 'd', 1);
    try nfa.addTransition(1, 'e', 0);
    try nfa.addTransition(1, 'e', 3);
    try nfa.addTransition(3, null, 1);

    try nfa.designateStatesFinal(&[_]u32{3});

    try nfa.backUpEpsTransitions();
    var dfa = try nfa.toPowersetConstructedDFA();
    try expect(dfa.isInLanguage("abed"));
    try expect(dfa.isInLanguage("abbbbbed"));
    try expect(dfa.isInLanguage("dbbbbbeceecebbbed"));
    // TODO more words
}

pub fn main() !void {
    const writer = std.io.getStdOut().writer();
    //const a = RegEx.initLiteralChar('a');
    //const b = RegEx.initLiteralChar('b');
    //
    //const aOrB = RegEx.initOperator(Token.Kind.Union, &a, &b);
    //try aOrB.printDOTRoot(writer);

    //const input = "xyz|w*(abc)*de*f";

    //var tok = try Tokenizer.init(input);
    //defer tok.deinit();
    //const regex = try RegEx.parseExpr(0, &tok);
    //assert(!tok.hasNext(), "expected EOF, but there were tokens left", .{});
    //try regex.printDOTRoot(writer);

    var nfa = try RegExNFA.init();
    try nfa.addStates(4);
    try nfa.addTransition(0, null, 2);
    try nfa.addTransition(0, 'a', 1);
    try nfa.addTransition(1, 'b', 1);
    try nfa.addTransition(2, 'c', 1);
    try nfa.addTransition(2, 'd', 3);
    try nfa.addTransition(2, 'd', 1);
    try nfa.addTransition(1, 'e', 0);
    try nfa.addTransition(1, 'e', 3);
    try nfa.addTransition(3, null, 1);

    try nfa.designateStatesFinal(&[_]u32{3});
    //var nfaAsFA = FiniteAutomaton{.nfa = nfa};
    //try nfaAsFA.printDOT(writer);

    try nfa.backUpEpsTransitions();
    var dfa = try nfa.toPowersetConstructedDFA();
    var dfaAsFA = FiniteAutomaton{.dfa = dfa};
    try dfaAsFA.printDOT(writer);

}
