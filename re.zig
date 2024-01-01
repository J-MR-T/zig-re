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

// sorted array set. does not suppport removal
pub fn ArraySet(comptime T:type, comptime comparatorFn:(fn (T, T) i8 )) type {
    return struct {
        items:[]T,
        internalAllocator:std.mem.Allocator,
        internalSlice:[]T,

        const InsertOpts = struct{
            ReplaceExisting:bool, // important for example if this is a key/value map and comparator fn only compares the key
            AssumeCapacity:bool,
            LinearInsertionSearch:bool,
            DontSort:bool,
        };

        const DefaultInsertOpts = .{.ReplaceExisting = false, .AssumeCapacity = false, .LinearInsertionSearch = false, .DontSort = false};

        pub fn init(allocator:std.mem.Allocator) !@This() {
            var self = @This(){
                .items = undefined,
                .internalSlice = try allocator.alloc(T, 0),
                .internalAllocator = allocator,
            };
            self.items = self.internalSlice[0..];
            return self;
        }

        pub fn deinit(self:@This()) void {
            self.internalAllocator.free(self.internalSlice);
        }

        pub fn ensureTotalCapacity(self:*@This(), minNewCapacity:usize) std.mem.Allocator.Error!void {
            if(minNewCapacity > self.internalSlice.len) {
                // from array_list.zig
                var betterCapacity = self.internalSlice.len;
                while (betterCapacity < minNewCapacity){
                    // saturating addition
                    betterCapacity +|= betterCapacity / 2 + 8;
                }

                // can't/shouldn't use realloc:
                // - can't use it on the items slice, because the size has to match the original allocation size
                // - shouldn't use it on the internalSlice, because that would copy even the unused capacity
                const old = self.internalSlice;
                self.internalSlice = try self.internalAllocator.alloc(T, betterCapacity);
                @memcpy(self.internalSlice[0..self.items.len], self.items);
                self.internalAllocator.free(old);

                self.items = self.internalSlice[0..self.items.len];
            }
        }

        pub fn ensureUnusedCapacity(self:*@This(), newCapacity:usize) std.mem.Allocator.Error!void {
            try self.ensureTotalCapacity(self.internalSlice.len + newCapacity);
        }

        pub fn resize(self:*@This(), newSize:usize) std.mem.Allocator.Error!void {
            try self.ensureTotalCapacity(newSize);
            self.items.len = newSize;
        }

        pub fn sort(self:*@This()) void {
            std.sort.pdq(T ,self.items, .{}, struct{
                pub fn f(_:@TypeOf(.{}), a:T, b:T) bool {
                    return comparatorFn(a, b) < 0;
                }
            }.f);
        }

        pub fn insert(self:*@This(), itemToInsert:T, comptime opts:InsertOpts) std.mem.Allocator.Error!void{
            if(opts.DontSort){
                if(!opts.AssumeCapacity)
                    try self.ensureUnusedCapacity(1);
                self.items.len += 1;
                self.items[self.items.len-1] = itemToInsert;
                return;
            }

            var left: usize = 0;
            var right: usize = self.items.len;

            if(opts.LinearInsertionSearch){
                while(comparatorFn(itemToInsert, self.items[left]) == 1 and left < right){
                    left += 1;
                }

                if(comparatorFn(itemToInsert, self.items[left]) == 0) {
                    if(opts.ReplaceExisting){
                        self.items[left] = itemToInsert;
                    }
                    return;
                }
                // otherwise left points to the first element that is greater than the item to insert
            }else{
                // binary search, but we can't use the std.sort one, because we need to insert if not found
                // so just copy that one and change it :
                while (left < right) {
                    // Avoid overflowing in the midpoint calculation
                    const mid = left + (right - left) / 2;
                    // Compare the key with the midpoint element
                    const comparison =  comparatorFn(itemToInsert, self.items[mid]);
                    if(comparison < 0){
                        // less
                        right = mid;
                    }else if(comparison > 0){
                        // greater
                        left = mid + 1;
                    }else{
                        // equal
                        // go to next, the state already exists in the combined state set
                        if(opts.ReplaceExisting){
                            // replace:
                            self.items[mid] = itemToInsert;
                        }
                        return;
                    }
                }
                assert(left == right, "after binary search to insert, we should be left with a definitive insertion point", .{});
            }

            const insertBefore = left;

            // we should insert if we reach this point -> reserve capacity
            if(!opts.AssumeCapacity)
                try self.ensureTotalCapacity(self.items.len + 1);

            // let the `items` slice know that it has grown
            self.items.len += 1;

            // assert sufficient capacity
            assert(insertBefore < self.items.len, "Insert out of capacity", .{});

            // shift everything to the right
            std.mem.copyBackwards(T, self.internalSlice[insertBefore+1..], self.internalSlice[insertBefore..(self.items.len - 1)]); // -1: old item length

            // insert
            self.items[insertBefore] = itemToInsert;
        }
    };

}

fn oldIntCast(x:anytype, comptime ResultType:type) ResultType {
    const result:ResultType = @intCast(x);
    return result;
}

// TODO there has to be a better way to 'save' the Key Type locally somehow, to avoid code dupe
fn keyCompare(comptime T:type, comptime compare:fn(@typeInfo(T).Struct.fields[0].type, @typeInfo(T).Struct.fields[0].type) i8) fn(T, T) i8 {
    return struct {
        pub fn f(a:T, b:T) i8 {
            return compare(a[0], b[0]);
        }
    }.f;
}

test "test array set" {
    const comparator = struct {fn f(a:u32, b:u32) i8 {
        // TODO the casting is of course not optimal
        const c:i32 = oldIntCast(a, i32) - oldIntCast(b, i32);
        return @intCast(@max(@min(c, 1), -1));
    }}.f;
    try expect(comparator(1, 2) < 0);
    try expect(comparator(4, 2) > 0);
    try expect(comparator(2, 2) == 0);

    const T = ArraySet(u32, comparator);
    var set = try T.init(allocer);
    const insertionOpts = T.DefaultInsertOpts;
    try set.insert(5, insertionOpts);
    try expect(std.mem.eql(u32, set.items, &[1]u32{5}));
    try set.insert(2, insertionOpts);
    try expect(std.mem.eql(u32, set.items, &[2]u32{2,5}));
    try set.insert(7, insertionOpts);
    try expect(std.mem.eql(u32, set.items, &[3]u32{2,5,7}));
    try set.insert(0, insertionOpts);
    try expect(std.mem.eql(u32, set.items, &[4]u32{0,2,5,7}));

    var set2 = try ArraySet(u32, comparator).init(allocer);
    const insertionOpts2 = .{.LinearInsertionSearch = false, .AssumeCapacity = false, .ReplaceExisting = false, .DontSort = true};
    try set2.insert(5, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[1]u32{5}));
    try set2.insert(2, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[2]u32{5,2}));
    try set2.insert(7, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[3]u32{5,2,7}));
    try set2.insert(0, insertionOpts2);

    for (set2.items) |item| {
        std.debug.print("{}\n", .{item});
    }

    try expect(std.mem.eql(u32, set2.items, &[4]u32{5,2,7,0}));
    set2.sort();
    try expect(std.mem.eql(u32, set2.items, &[4]u32{0,2,5,7}));
}

test "use array set as map" {
    const T = Tuple(&[2]type{u32, u32});

    const comp = keyCompare(T, struct {fn f(a:u32, b:u32) i8 {
        // TODO the casting is of course not optimal
        const c:i32 = oldIntCast(a, i32) - oldIntCast(b, i32);
        return @intCast(@max(@min(c, 1), -1));
    }}.f);

    const MapT = ArraySet(T, comp);
    var set = try MapT.init(allocer);
    const insertionOpts = MapT.DefaultInsertOpts;
    // do x^2 for testing

    var rnd = std.rand.DefaultPrng.init(0);
    for (0..100) |_| {
        const x = rnd.random().intRangeLessThan(u32, 0, 1 << 15);
        try set.insert(.{x, x*x}, insertionOpts);
    }

    var lastItem = set.items[0];
    for (set.items) |item| {
        // keys ([0]) should be sorted
        try expect(item[0] >= lastItem[0]);
        lastItem = item;

        // and values ([1]) should be correctd 
        try expect(item[1] == item[0]*item[0]);
    }
}

const Token = struct {
    char:u8,
    kind:Kind,

    pub const Kind = enum {
        Char,
        // TODO implement
        //AnyChar,
        Concat,
        Union,
        Kleen,
        LParen,
        RParen,

        // hope that the compiler knows that this is often used at comptime
        pub fn precedenceAndChar(self:@This()) struct{prec:u8, char:u8} {
            return switch(self){
                Kind.Char    => .{.prec = 0, .char = 'x'},
                //Kind.AnyChar => .{.prec = 0, .char = '.'},
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
                //Kind.AnyChar.precedenceAndChar().char => Kind.AnyChar,
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
                //Kind.AnyChar => true,
                Kind.Kleen   => true,
                Kind.RParen  => true,
                else         => false
            };
        }
        pub fn canConcatToLeft(self:@This()) bool {
            return switch(self){
                Kind.Char    => true,
                //Kind.AnyChar => true,
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
    left:?*RegEx,
    right:?*RegEx,
    kind:Token.Kind,
    char:u8,

    // for DFA conversion
    nfaStartState:?u32,
    nfaEndState:?u32,

    pub fn initLiteralChar(char:u8) @This() {
        return RegEx{
            .left = null,
            .right = null,
            .kind = Token.Kind.Char,
            .char = char,
            .nfaStartState = null,
            .nfaEndState = null,
        };
    }

    pub fn initOperator(kind:Token.Kind, left:*RegEx, right:?*RegEx) @This() {
        return RegEx{
            .left = left,
            .right = right,
            .kind = kind,
            .char = kind.precedenceAndChar().char,
            .nfaStartState = null,
            .nfaEndState = null,
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
            // let the upper level parse 'unknown operators' (in this case anything but the binary operators)
            var operatorKind = tok.peek().kind; // we peek, because if we return inside the loop, the upper level needs to consume that token
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

    pub fn isOperator(self:RegEx) bool {
        // if left is null (i.e. this is a leaf), right must be null too
        assert(self.left != null or self.right == null, "regex has no left operand, but right operand is not null", .{});
        return self.left != null;
    }

    pub fn printDOTRoot(self:RegEx, writer:anytype) !void {
        try writer.print("digraph RegEx {{", .{});
        try self.printDOTInternal(writer, 1);
        try writer.print("}}\n", .{});
    }

    pub fn toDFA(self:*@This()) !RegExDFA {
        // broad overview: convert regex to eps-nfa to nfa to dfa.
        // vague idea (mostly my own, no idea if this is good): 
        // 1. iterate in post order over the AST, create and save start and end states for each operator node (all except the leafs), and connect the with the transitions. Distinguish between whether the operator has leaf- (i.e. char-) operands or other operator operands
        //    -> this implies the construction will not be that efficient, as we sometimes need to create new states + transitions to be able to save only one start/end state (for example for |)
        // 2. designate full start/end states for the whole regex
        // 3. back up eps transitions
        // 4. convert to dfa

        // edge case: no operators, just a single char
        if(!self.isOperator()) {
            assert(self.right == null, "regex has no left operand, but right operand is not null", .{});

            var dfa = try RegExDFA.init();
            dfa.startState = try dfa.addState();
            try dfa.designateStatesFinal(&[1]u32{@truncate(dfa.startState)});
            try dfa.transitions[dfa.startState].put(self.char, dfa.startState);

            // TODO handle AnyChar here as soon as it's implemented

            return dfa;
        }

        var nfa = try RegExNFA.init();

        const VisitKind = enum{WAY_DOWN, WAY_UP};

        const VisitInfo = struct{regex:*RegEx, kind:VisitKind};
        var worklist = try initArrayListLikeWithElements(allocer, std.ArrayList(VisitInfo), &[1]VisitInfo{.{.regex = self, .kind = VisitKind.WAY_DOWN}});

        while(worklist.items.len > 0) {
            try worklist.ensureUnusedCapacity(2);
            // only do this after enough capacity for at least two more items has been reserved, so that this pointer is not invalidated during appending
            var cur:*VisitInfo = &worklist.items[worklist.items.len - 1];

            // should never have a leaf/char in the worklist
            assert(cur.regex.isOperator(), "worklist contained leaf/char", .{});
            const left = cur.regex.left orelse unreachable;

            switch(cur.kind){
                VisitKind.WAY_DOWN => {
                    // TODO ensure we're constructing a post order traversal on the way down

                    // prepare next visit
                    defer cur.kind = VisitKind.WAY_UP;

                    if(left.isOperator())
                        worklist.appendAssumeCapacity(.{.regex = left, .kind = VisitKind.WAY_DOWN});

                    if(cur.regex.right) |right| if (right.isOperator())
                        worklist.appendAssumeCapacity(.{.regex = right, .kind = VisitKind.WAY_DOWN});

                    // if we haven't appended anything now, we will visit 'ourselves' immediately again, so we start the way up on this path
                },
                VisitKind.WAY_UP => {
                    debugLog("up: {}\n", .{cur.regex});

                    // TODO do all of the actual processing only on the way up
                    defer _ = worklist.pop(); // remove the current item from the worklist after dealing with it

                    // we can check whether left/right have a start/end state yet to determine whether we can just connect them, or we need to create a new start/end state (+transitions)

                    // TODO this can be optimized, we don't need a new start/end state in every case. But it does not save huge amounts of time, we will just have a bunch of unused states in the nfa, that won't be added to the dfa, because they're never reached from the start state
                    try nfa.addStates(2);
                    cur.regex.nfaStartState = nfa.numStates - 2;
                    const curStartState = cur.regex.nfaStartState orelse unreachable;
                    cur.regex.nfaEndState = nfa.numStates - 1;
                    const curEndState = cur.regex.nfaEndState orelse unreachable;

                    // in the operator, connect the start/end states of the operands with the operator
                    switch(cur.regex.kind){
                        Token.Kind.Union => {
                            const right = cur.regex.right orelse unreachable;

                            if(!left.isOperator()){
                                try nfa.addTransition(curStartState, left.char, curEndState);
                            }else{
                                // if it is an operator, we have visited it before, so it has a start/end state, so we can just connect it
                                try nfa.addTransition(left.nfaEndState orelse unreachable, null, curEndState);

                                // also connect the start state of the operator with the start state of the left operand
                                try nfa.addTransition(curStartState, null, left.nfaStartState orelse unreachable);
                            }

                            if(!right.isOperator()){
                                try nfa.addTransition(curStartState, right.char, curEndState);
                            }else{
                                // same as left
                                try nfa.addTransition(right.nfaEndState orelse unreachable, null, curEndState);
                                try nfa.addTransition(curStartState, null, right.nfaStartState orelse unreachable);
                            }
                            // sidenote: see? this is exactly why ever programming language needs the ability to use 'local functions'/lambdas for readability. Do you hear me, Zig? :. Don't even need to be real functions in the end, can just inline all of them (and forbid non-inlinable ones)
                        },
                        Token.Kind.Concat => {
                            const right = cur.regex.right orelse unreachable;

                            if(left.isOperator() and right.isOperator()){
                                // if both are operators, we have visited them before, so they have start/end states, so we can just connect them
                                try nfa.addTransition(left.nfaEndState orelse unreachable, null, right.nfaStartState orelse unreachable);
                                // and set the start/end of this operator to the start/end of the operands
                                cur.regex.nfaStartState = left.nfaStartState orelse unreachable;
                                cur.regex.nfaEndState = right.nfaEndState orelse unreachable;
                            }else if(left.isOperator()){
                                // if only left is an operator, we can take the existing end state of left and connect it with the char of right to the new end state
                                try nfa.addTransition(left.nfaEndState orelse unreachable, right.char, curEndState);
                                cur.regex.nfaStartState = left.nfaStartState orelse unreachable;
                            }else if(right.isOperator()){
                                // same as left
                                try nfa.addTransition(curStartState, left.char, right.nfaStartState orelse unreachable);
                                cur.regex.nfaEndState = right.nfaEndState orelse unreachable;
                            }else{
                                // if both are chars, we need one more state in between
                                const inBetweeny = try nfa.addState();
                                try nfa.addTransition(curStartState, left.char, inBetweeny);
                                try nfa.addTransition(inBetweeny, right.char, curEndState);
                            }

                        },
                        Token.Kind.Kleen => {
                            if(left.isOperator()){
                                // we just reuse all of the operator and connect the end state with the start state
                                try nfa.addTransition(left.nfaEndState orelse unreachable, null, left.nfaStartState orelse unreachable);
                                cur.regex.nfaStartState = left.nfaStartState orelse unreachable;
                                cur.regex.nfaEndState = left.nfaEndState orelse unreachable;
                            }else{
                                // just use the start state as start/end
                                // and add a transition to itself
                                try nfa.addTransition(curStartState, left.char, curStartState);
                                cur.regex.nfaEndState = curStartState;
                            }
                        },
                        else => unreachable,
                    }
                },
            }
        }

        nfa.startState = self.nfaStartState orelse unreachable;
        try nfa.designateStatesFinal(&[1]u32{self.nfaEndState orelse unreachable});


        try nfa.backUpEpsTransitions();
        return try nfa.toPowersetConstructedDFA();
    }

    // mostly for debugging
    pub fn format(value: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) std.os.WriteError!void {
        try writer.print("Itself: {c}", .{value.char});
        if(value.left) |left| if(!left.isOperator())
            try writer.print(" Left: {c}", .{left.char});

        if(value.right) |right| if(!right.isOperator())
            try writer.print(" Right: {c}", .{right.char});
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

const FiniteAutomaton = union(enum){
    dfa:*RegExDFA,
    nfa:*RegExNFA,

    pub fn printDOT(self:FiniteAutomaton, writer:anytype) !void {
        try writer.print("digraph ", .{});
        switch(self){
            FiniteAutomaton.dfa => try writer.print("DFA", .{}),
            FiniteAutomaton.nfa => try writer.print("NFA", .{}),
        }
        try writer.print("{{ node[shape=circle];", .{});

        const startState = switch(self){
            inline else => |case| case.startState
        };

        const states = switch(self){
            inline else => |case| case.numStates
        };

        const finalStates = switch(self){
            inline else => |case| case.finalStates
        };

        const numStates = switch(self){
            inline else => |case| case.numStates
        };

        for(0..states) |curStateI| {
            const curState:u32 = @truncate(curStateI);

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
                    if(curState > nfa.transitions.len)
                        continue;

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
        }

        // for start state
        try writer.print("n{}[label=\"\",style=\"invis\"];n{} -> n{}; ", .{numStates, numStates, startState});

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
                // TODO this is wrong, needs to disallow duplicates
                // TODO should probably make a sorted datastructure, would be helpful in tons of cases, like for set-like datastructures and more efficient maps than hashmaps
                try entry.value_ptr.*.appendSlice(transition.value_ptr.*.items);
            }
        }
    }

    // does not eliminate, but 'fill' epsilon transitions, so that they can be ignored from now on (because the language of the NFA after this function is the same with or without them)
    pub fn backUpEpsTransitions(self:*@This()) !void {
        // TODO this is wrong, as it misses transitive epsilon transitions
        for(0.., self.transitions) |state,*transitionsFromState| {
            if(transitionsFromState.get(null)) |epsTransitionsFromState| {
                // TODO solution to transitive epsilons: do this as long as it adds anything

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
                assert(self.transitions.len > curNfaState, "nfa state out of bounds, nfa is invalid", .{});

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
                                // so just copy that one and change it :
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

test "regex to dfa" {
    const input = "xyz|w*(abc)*de*f";

    var tok = try Tokenizer.init(input);
    defer tok.deinit();
    const regex = try RegEx.parseExpr(0, &tok);
    assert(!tok.hasNext(), "expected EOF, but there were tokens left", .{});

    var dfa = try regex.toDFA();
    //try (FiniteAutomaton{.dfa = dfa}).printDOT(std.io.getStdOut().writer());

    try expect(dfa.isInLanguage("xyz"));
    try expect(!dfa.isInLanguage("xz"));
    try expect(!dfa.isInLanguage("xy"));
    try expect(!dfa.isInLanguage("x"));
    try expect(!dfa.isInLanguage("y"));
    try expect(!dfa.isInLanguage("z"));

    //try expect(dfa.isInLanguage("wwwwwwwwdf"));
    //try expect(dfa.isInLanguage("df"));
    //try expect(dfa.isInLanguage("wabcabcdeeef"));
    //try expect(dfa.isInLanguage("wwwwabcabcabcdeeef"));
}

pub fn main() !void {
    const writer = std.io.getStdOut().writer();
    _ = writer;
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

    //var nfa = try RegExNFA.init();
    //try nfa.addStates(4);
    //try nfa.addTransition(0, null, 2);
    //try nfa.addTransition(0, 'a', 1);
    //try nfa.addTransition(1, 'b', 1);
    //try nfa.addTransition(2, 'c', 1);
    //try nfa.addTransition(2, 'd', 3);
    //try nfa.addTransition(2, 'd', 1);
    //try nfa.addTransition(1, 'e', 0);
    //try nfa.addTransition(1, 'e', 3);
    //try nfa.addTransition(3, null, 1);
    //
    //try nfa.designateStatesFinal(&[_]u32{3});
    //var nfaAsFA = FiniteAutomaton{.nfa = nfa};
    //try nfaAsFA.printDOT(writer);

    //try nfa.backUpEpsTransitions();
    //var dfa = try nfa.toPowersetConstructedDFA();
    //var dfaAsFA = FiniteAutomaton{.dfa = dfa};
    //try dfaAsFA.printDOT(writer);

    const comparator = struct {fn f(a:u32, b:u32) i8 {
        // TODO the casting is of course not optimal
        const c:i32 = oldIntCast(a, i32) - oldIntCast(b, i32);
        return @intCast(@max(@min(c, 1), -1));
    }}.f;
    try expect(comparator(1, 2) < 0);
    try expect(comparator(4, 2) > 0);
    try expect(comparator(2, 2) == 0);

    var set = try ArraySet(u32, comparator).init(allocer);
    const insertionOpts = .{.LinearInsertionSearch = false, .AssumeCapacity = false, .ReplaceExisting = false};
    try set.insert(5, insertionOpts);
    try set.insert(2, insertionOpts);
    try set.insert(7, insertionOpts);
    try set.insert(0, insertionOpts);
}
