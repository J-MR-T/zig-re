const std = @import("std");
const easyAllocer = std.heap.c_allocator;
const Allocator = std.mem.Allocator;
fn assert(condition:bool, comptime message:[]const u8, args:anytype) void {
    if (!condition) {
        std.debug.print("\n-----------------------\nAssertion failed: " ++ message ++ "\n-----------------------\nTrace:\n", args);
        unreachable;
    }
}
fn debugLog(comptime message:[]const u8, args:anytype) void {
    std.debug.print(message ++ "\n", args);
}

const Tuple = std.meta.Tuple;
const Order = std.math.Order;

fn initArrayListLikeWithElements(allocator:Allocator, comptime ArrayListType:type, elementsSlice:anytype) !ArrayListType{
    var arrayListLike = try ArrayListType.initCapacity(allocator, elementsSlice.len);
    errdefer arrayListLike.deinit();

    try arrayListLike.appendSlice(elementsSlice);

    return arrayListLike;
}

fn makeOrder(comptime T:type) fn (T, T) Order {
    return struct {
        pub fn f(a:T, b:T) Order {
            return std.math.order(a, b);
        }
    }.f;
}

// sorted array set. does not suppport removal
pub fn ArraySet(comptime T:type, comptime comparatorFn:(fn (T, T) Order)) type {
    return struct {
        items:[]T,
        internalAllocator:Allocator,
        internalSlice:[]T,

        const InsertOpts = struct{
            ReplaceExisting:bool       = false, // important for example if this is a key/value map and comparator fn only compares the key
            AssumeCapacity:bool        = false,
            LinearInsertionSearch:bool = false,
            DontSort:bool              = false,
        };

        const FindOpts = struct{
            MakeSpaceForNewIfNotFound:bool = false,
            AssumeCapacity:bool            = false,
            LinearInsertionSearch:bool     = false,
        };
        pub fn init(allocator:Allocator) !@This() {
            var self = @This(){
                .items = undefined,
                .internalSlice = try allocator.alloc(T, 0),
                .internalAllocator = allocator,
            };
            self.items = self.internalSlice[0..];
            return self;
        }

        pub fn initCapacity(allocator:Allocator, capacity:usize) Allocator.Error!@This() {
            var self = @This(){
                .items = undefined,
                .internalSlice = try allocator.alloc(T, capacity),
                .internalAllocator = allocator,
            };
            // pay attention not to use the internalSlice here as above, because the items slice should not be filled with undefined items, it should just have the capacity
            self.items.ptr = self.internalSlice.ptr;
            self.items.len = 0;
            return self;
        }

        pub fn initElements(allocator:Allocator, elementsSlice:anytype) Allocator.Error!@This() {
            var self = try initCapacity(allocator, elementsSlice.len);
            for (elementsSlice) |item| {
                try self.insert(item, .{.AssumeCapacity = true});
            }
            return self;
        }

        pub fn deinit(self:@This()) void {
            self.internalAllocator.free(self.internalSlice);
        }

        pub fn ensureTotalCapacity(self:*@This(), minNewCapacity:usize) Allocator.Error!void {
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

        pub fn ensureUnusedCapacity(self:*@This(), newCapacity:usize) Allocator.Error!void {
            try self.ensureTotalCapacity(self.items.len + newCapacity);
        }

        pub fn resize(self:*@This(), newSize:usize) Allocator.Error!void {
            try self.ensureTotalCapacity(newSize);
            self.items.len = newSize;
        }

        pub fn sort(self:*@This()) void {
            std.sort.pdq(T ,self.items, .{}, struct{
                pub fn f(_:@TypeOf(.{}), a:T, b:T) bool {
                    return comparatorFn(a, b) == Order.lt;
                }
            }.f);
        }

        const SpotInfo = struct{item_ptr:*T, found_existing:bool};

        pub fn insert(self:*@This(), itemToInsert:T, comptime opts:InsertOpts) Allocator.Error!void{
            _ = try insertAndGet(self, itemToInsert, opts);
        }

        pub fn insertAndGet(self:*@This(), itemToInsert:T, comptime opts:InsertOpts) Allocator.Error!SpotInfo {
            if(opts.DontSort){
                if(opts.LinearInsertionSearch)
                    @compileError("LinearInsertionSearch not applicable when DontSort is set");
                if(opts.ReplaceExisting)
                    @compileError("ReplaceExisting not applicable when DontSort is set");

                if(!opts.AssumeCapacity)
                    try self.ensureUnusedCapacity(1);
                self.items.len += 1;
                self.items[self.items.len-1] = itemToInsert;
                return .{.item_ptr = &self.items[self.items.len-1], .found_existing = false};
            }

            var findResults = try self.findSpot(itemToInsert, .{.MakeSpaceForNewIfNotFound = true, .AssumeCapacity = opts.AssumeCapacity, .LinearInsertionSearch = opts.LinearInsertionSearch});
            // if we didnt find it, or we should replace it, write to it
            if(!findResults.found_existing or opts.ReplaceExisting)
                findResults.item_ptr.* = itemToInsert;

            // results are still correct
            return findResults;
        }

        // invalidates pointers and capacity guarantees in all cases (!)
        // this could also be done sort of in-place with sufficient guarantees, but that is unnecessarily complex for now
        pub fn addAll(a:*@This(), b:@This()) Allocator.Error!void {
            if(a.items.ptr == b.items.ptr){
                assert(a.items.len == b.items.len, "addAll called on the same set with different lengths", .{});
                return;
            }

            var self = a;

            // allocate a new array with the combined capacity, that will become the self.items array later
            var newInternalSlice = try a.internalAllocator.alloc(T, a.items.len + b.items.len);

            // merge the two basically like in mergesort, but take care to deduplicate them

            var aI:usize = 0;
            var bI:usize = 0;
            var newI:usize = 0;

            var actualNewLen:usize = newInternalSlice.len;

            while(true) : (newI += 1) {
                if(aI >= a.items.len){
                    // a is empty, just copy the rest of b (deduplicate the joint)
                    if(newI != 0 and comparatorFn(newInternalSlice[newI - 1], b.items[bI]) == Order.eq){
                        bI += 1;
                        actualNewLen -= 1;
                    }

                    if(bI >= b.items.len)
                        // b is empty too, we're done
                        break;

                    @memcpy(newInternalSlice[newI..actualNewLen], b.items[bI..]);
                    break;
                }else if(bI >= b.items.len){
                    // same thing, b is empty, so copy the rest of a, with deduplication
                    if(newI != 0 and comparatorFn(newInternalSlice[newI - 1], a.items[aI]) == Order.eq){
                        aI += 1;
                        actualNewLen -= 1;
                    }

                    if(aI >= a.items.len)
                        // a is empty too, we're done
                        break;

                    @memcpy(newInternalSlice[newI..actualNewLen], a.items[aI..]);
                    break;
                }else
                    // otherwise copy the smaller one
                if(comparatorFn(a.items[aI], b.items[bI]) == Order.lt){
                    // deduplicate
                    if(newI != 0 and comparatorFn(newInternalSlice[newI - 1], a.items[aI]) == Order.eq){
                        actualNewLen -= 1;
                        // don't increment newI, so we overwrite the duplicate
                        newI -= 1;
                    }else{
                        newInternalSlice[newI] = a.items[aI];
                    }
                    aI += 1;
                }else{
                    // deduplicate
                    if(newI != 0 and comparatorFn(newInternalSlice[newI - 1], b.items[bI]) == Order.eq){
                        actualNewLen -= 1;
                        // don't increment newI, so we overwrite the duplicate
                        newI -= 1;
                    }else{
                        newInternalSlice[newI] = b.items[bI];
                    }
                    bI += 1;
                }
            } 

            // replace the old self array with the new one
            self.internalAllocator.free(self.internalSlice);
            self.internalSlice = newInternalSlice;
            self.items = newInternalSlice[0..actualNewLen];
        }

        // this is not very efficient, as this set is not really designed to have elements removed from frequently. Has to move O(n) elements in the worst case
        // returns whether it removed something
        // never shrinks the internal array
        pub fn remove(self:*@This(), itemToRemove:T, comptime findOpts:FindOpts) bool {
            if(findOpts.MakeSpaceForNewIfNotFound)
                @compileError("MakeSpaceForNewIfNotFound not applicable for remove");

            const spot = self.findSpot(itemToRemove, findOpts) catch unreachable;
            if(spot.found_existing){
                const i = (@intFromPtr(spot.item_ptr) - @intFromPtr(self.items.ptr))/@sizeOf(T);
                std.mem.copyForwards(T, self.items[i..self.items.len-1], self.items[i+1..self.items.len]);
                self.items.len -= 1;
                return true;
            }
            return false;
        }

        // returns whether the set contains the item
        pub fn contains(self:*const @This(), itemToFind:T) bool {
            return self.find(itemToFind) != null;
        }

        pub fn containsKey(self:*const @This(), keyToFind:@typeInfo(T).Struct.fields[0].type) bool {
            return self.findByKey(keyToFind) != null;
        }

        // finds the first item that is greater than or equal to the item to find using binary search
        pub fn find(self:*const @This(), itemToCompareAgainst:T) ?T{
            // can confidently @constCast, and ignore the error, because we don't modify anything (guaranteed by the implementation)
            const spot = @constCast(self).findSpot(itemToCompareAgainst, .{.MakeSpaceForNewIfNotFound = false, .AssumeCapacity = false, .LinearInsertionSearch = false}) catch unreachable;
            return if(spot.found_existing) spot.item_ptr.* else null;
        }

        // finds the first item that is greater than or equal to the item to find using linear search
        pub fn findLinear(self:*const @This(), itemToCompareAgainst:T) ?T{
            const spot = @constCast(self).findSpot(itemToCompareAgainst, .{.MakeSpaceForNewIfNotFound = false, .AssumeCapacity = false, .LinearInsertionSearch = true}) catch unreachable;
            return if(spot.found_existing) spot.item_ptr.* else null;
        }

        // finds 
        pub fn findByKey(self:*const @This(), keyToCompareAgainst:@typeInfo(T).Struct.fields[0].type) ?@typeInfo(T).Struct.fields[1].type{
            if(@typeInfo(T).Struct.fields.len != 2)
                @compileError("findByKey only works when this set is being used as a key value map, i.e. with two-long tuple elements");

            return (self.find(.{keyToCompareAgainst, undefined}) orelse return null)[1];
        }

        // only use this if you know what you're doing, try to use `contains`, the other `find...` function or `insert` if possible
        // finds the first item that is greater than or equal to the item to find and returns a pointer to it or the place it should be inserted if it does not exist, as well as whether or not it exists
        // if opts.MakeSpaceForNewIfNotFound is set, the array will be expanded and the returned pointer will point to the new item (undefined) item.
        // if opts.MakeSpaceForNewIfNotFound is not set, the returned pointer will be invalid (but sensible!), if .found_existing is false
        pub fn findSpot(self:*@This(), itemToCompareAgainst:T, comptime opts:FindOpts) !SpotInfo {
            if(!opts.MakeSpaceForNewIfNotFound and opts.AssumeCapacity)
                @compileError("Can't assume capacity if findSpot can not insert");

            var left: usize = 0;
            var right: usize = self.items.len;

            // in any of the cases where we find it, we can ignore opts.MakeSpaceForNewIfNotFound (obviously)
            if(opts.LinearInsertionSearch){
                while(comparatorFn(itemToCompareAgainst, self.items[left]) == Order.gt and left < right){
                    left += 1;
                }

                if(comparatorFn(itemToCompareAgainst, self.items[left]) == Order.eq) {
                    return .{.item_ptr = &self.items[left], .found_existing = true};
                }
                // otherwise left points to the first element that is greater than the item to insert -> insert before that 
            }else{
                // binary search, but we can't use the std.sort one, because we need to insert if not found
                // so just copy that one and change it :
                while (left < right) {
                    // Avoid overflowing in the midpoint calculation
                    const mid = left + (right - left) / 2;
                    // Compare the key with the midpoint element
                    switch(comparatorFn(itemToCompareAgainst, self.items[mid])){
                        Order.lt => right = mid,
                        Order.gt => left = mid + 1,
                        Order.eq => return .{.item_ptr = &self.items[mid], .found_existing = true},
                    }
                }
                assert(left == right, "after binary search to insert, we should be left with a definitive insertion point", .{});
                // left again points to first element that is greater than the item to insert -> insert before that
            }

            // didn't find, return the insertion point (and possibly expand the array, and move the items)

            const firstGreater = left;

            // assert sensible insertion point
            assert(firstGreater <= self.items.len, "Find reached too far outside the array", .{});

            if(opts.MakeSpaceForNewIfNotFound){
                if(!opts.AssumeCapacity)
                    try self.ensureUnusedCapacity(1);

                // let the `items` slice know that it has grown
                self.items.len += 1;

                // shift everything to the right
                std.mem.copyBackwards(T, self.internalSlice[firstGreater+1..], self.internalSlice[firstGreater..(self.items.len - 1)]); // -1: old item length
            }

            return .{.item_ptr = @ptrCast(self.items.ptr + firstGreater), .found_existing = false};
        }

        // clones the set, uses the same allocator. Does not make any guarantees about the capacity of the new set, just that the actual elements are the same
        pub fn clone(self:@This()) !@This() {
            var theClone = try @This().initCapacity(self.internalAllocator, self.items.len);
            theClone.items.len = self.items.len;
            @memcpy(theClone.items, self.items);
            return theClone;
        }

        pub fn debugPrint(self:@This()) void {
            for (self.items) |item| {
                std.debug.print("{}, ", .{item});
            }
            std.debug.print("\n", .{});
        }
    };

}

fn oldIntCast(x:anytype, comptime ResultType:type) ResultType {
    const result:ResultType = @intCast(x);
    return result;
}

// TODO there has to be a better way to 'save' the Key Type locally somehow, to avoid code dupe
fn keyCompare(comptime T:type, comptime compare:fn(@typeInfo(T).Struct.fields[0].type, @typeInfo(T).Struct.fields[0].type) Order) fn(T, T) Order {
    return struct {
        pub fn f(a:T, b:T) Order {
            return compare(a[0], b[0]);
        }
    }.f;
}

test "test array set" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const T = ArraySet(u32, makeOrder(u32));
    var set = try T.init(arena.allocator());
    try set.insert(5, .{});
    try expect(std.mem.eql(u32, set.items, &[1]u32{5}));
    try set.insert(2, .{});
    try expect(std.mem.eql(u32, set.items, &[2]u32{2,5}));
    try set.insert(7, .{});
    try expect(std.mem.eql(u32, set.items, &[3]u32{2,5,7}));
    try set.insert(0, .{});
    try expect(std.mem.eql(u32, set.items, &[4]u32{0,2,5,7}));

    var set2 = try ArraySet(u32, makeOrder(u32)).init(arena.allocator());
    const insertionOpts2:T.InsertOpts = .{.DontSort = true};
    try set2.insert(5, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[1]u32{5}));
    try set2.insert(2, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[2]u32{5,2}));
    try set2.insert(7, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[3]u32{5,2,7}));
    try set2.insert(0, insertionOpts2);
    try expect(std.mem.eql(u32, set2.items, &[4]u32{5,2,7,0}));

    set2.sort();
    try expect(std.mem.eql(u32, set2.items, &[4]u32{0,2,5,7}));

    try expect(set2.remove(2, .{}) == true);
    try expect(std.mem.eql(u32, set2.items, &[3]u32{0,5,7}));
    try expect(set2.remove(3, .{}) == false);
    try expect(std.mem.eql(u32, set2.items, &[3]u32{0,5,7}));
    try expect(set2.remove(4, .{}) == false);
    try expect(std.mem.eql(u32, set2.items, &[3]u32{0,5,7}));
    try expect(set2.remove(5, .{}) == true);
    try expect(std.mem.eql(u32, set2.items, &[2]u32{0,7}));
}

test "array set addAll" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const insertionOpts = .{.LinearInsertionSearch = false, .AssumeCapacity = false, .ReplaceExisting = false, .DontSort = false};
    var set1 = try ArraySet(u32, makeOrder(u32)).init(arena.allocator());
    try set1.insert(5, insertionOpts);
    try set1.insert(2, insertionOpts);
    try set1.insert(7, insertionOpts);
    try set1.insert(0, insertionOpts);

    var set2 = try ArraySet(u32, makeOrder(u32)).init(arena.allocator());
    try set2.insert(4, insertionOpts);
    try set2.insert(1, insertionOpts);
    try set2.insert(6, insertionOpts);
    try set2.insert(3, insertionOpts);

    try set1.addAll(set2);

    try expect(std.mem.eql(u32, set1.items, &[8]u32{0,1,2,3,4,5,6,7}));


    // add random stuff to the two sets, compare against a single set
    const numStuffToInsert = 10000;

    set1 = try ArraySet(u32, makeOrder(u32)).initCapacity(arena.allocator(), numStuffToInsert * 2);
    set2 = try ArraySet(u32, makeOrder(u32)).initCapacity(arena.allocator(), numStuffToInsert);

    var correctSet = try ArraySet(u32, makeOrder(u32)).initCapacity(arena.allocator(), numStuffToInsert * 2 );

    var rnd = std.rand.DefaultPrng.init(0);
    for(0..numStuffToInsert) |_| {
        var rand1 = rnd.random().intRangeLessThan(u32, 0, 1000);
        var rand2 = rnd.random().intRangeLessThan(u32, 0, 1000);

        try set1.insert(rand1, insertionOpts);
        try set2.insert(rand2, insertionOpts);

        try correctSet.insert(rand1, insertionOpts);
        try correctSet.insert(rand2, insertionOpts);

        try set1.addAll(set2);

        if(!std.mem.eql(u32, set1.items, correctSet.items)){
            debugLog("added set (size: {}):", .{set1.items.len});
            set1.debugPrint();
            debugLog("check set (size: {}):", .{correctSet.items.len});
            correctSet.debugPrint();
            try expect(false);
        }
    }

}

test "use array set as map" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const T = Tuple(&[2]type{u32, u32});

    const S = struct{
        fn order_u32(a:u32, b:u32) Order {
            return std.math.order(a, b);
        }
    };

    const comp = keyCompare(T, S.order_u32);

    const MapT = ArraySet(T, comp);
    var set = try MapT.init(arena.allocator());
    const insertionOpts:MapT.InsertOpts = .{};
    // do x^2 for testing

    var rnd = std.rand.DefaultPrng.init(0);
    for (0..10000) |i| {
        _ = i;
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

const SyntaxError = error{InvalidToken};
const ParseError = error{OutOfMemory} || SyntaxError;

const Tokenizer = struct {
    tokens:[]Token,
    cur:u32,
    internalAllocator:Allocator,

    // can be used without Tokenizer, but tokenizer is more convenient
    fn tokenize(input:[]const u8, allocer:Allocator) error{OutOfMemory}![]Token {
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

    pub fn init(input:[]const u8, allocer:Allocator) !@This() {
        const tokens = try tokenize(input, allocer);
        return Tokenizer{
            .tokens = tokens,
            .cur = 0,
            .internalAllocator = allocer,
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
        self.internalAllocator.free(self.tokens);
    }

    fn debugFmt(self:@This()) !std.ArrayList(u8) {
        var buf = try std.ArrayList(u8).initCapacity(easyAllocer, self.tokens.len);
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

    internalAllocator:Allocator,

    // for DFA conversion
    nfaStartState:?u32,
    nfaEndState:?u32,

    pub fn initLiteralChar(allocer:Allocator, char:u8) @This() {
        return RegEx{
            .left = null,
            .right = null,
            .kind = Token.Kind.Char,
            .char = char,
            .internalAllocator = allocer,
            .nfaStartState = null,
            .nfaEndState = null,
        };
    }

    pub fn initOperator(allocer:Allocator, kind:Token.Kind, left:*RegEx, right:?*RegEx) @This() {
        return RegEx{
            .left = left,
            .right = right,
            .kind = kind,
            .char = kind.precedenceAndChar().char,
            .internalAllocator = allocer,
            .nfaStartState = null,
            .nfaEndState = null,
        };
    }

    pub fn parsePrimaryExpr(allocer:Allocator, tok:*Tokenizer) ParseError!*@This() {
        var primary:*RegEx = undefined;
        if(tok.matchNext(Token.Kind.LParen, true)) {
            primary = try parseExpr(allocer, 0, tok);
            try tok.assertNext(Token.Kind.RParen);
        }else{
            primary = try allocer.create(RegEx);
            primary.* = initLiteralChar(allocer, tok.next().char);
        }

        if(tok.matchNext(Token.Kind.Kleen, true)) { // kleens prec is ignored because its the highest anyway
            var kleen = try allocer.create(RegEx);
            kleen.* = initOperator(allocer, Token.Kind.Kleen, primary, null);
            return kleen;
        }
        return primary;
    }

    // TODO expand with allocator choice
    pub fn parseExpr(allocer:Allocator, minPrec:u32, tok:*Tokenizer) ParseError!*@This() {
        var lhs = try parsePrimaryExpr(allocer, tok);
        while (tok.hasNext()) {
            // let the upper level parse 'unknown operators' (in this case anything but the binary operators)
            var operatorKind = tok.peek().kind; // we peek, because if we return inside the loop, the upper level needs to consume that token
            if(operatorKind != Token.Kind.Union and operatorKind != Token.Kind.Concat)
                return lhs;

            var prec = operatorKind.precedenceAndChar().prec;
            if (prec < minPrec)
                return lhs;

            _ = tok.next(); // consume operator



            var rhs = try parseExpr(allocer, prec + 1, tok); // always + 1, because we only have left-associative operators, so we want to bind the same operator again in the next depth, not in the one above
            var op = try easyAllocer.create(RegEx);
            op.* = initOperator(allocer, operatorKind, lhs, rhs);
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

            var dfa = try RegExDFA.init(self.internalAllocator);
            dfa.startState = try dfa.addState();
            try dfa.designateStatesFinal(&[1]u32{@truncate(dfa.startState)});
            try dfa.transitions[dfa.startState].insert(.{self.char, dfa.startState}, .{});

            // TODO handle AnyChar here as soon as it's implemented

            return dfa;
        }

        var arena = std.heap.ArenaAllocator.init(easyAllocer);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());

        const VisitKind = enum{WAY_DOWN, WAY_UP};

        const VisitInfo = struct{regex:*RegEx, kind:VisitKind};
        var worklist = try initArrayListLikeWithElements(arena.allocator(), std.ArrayList(VisitInfo), &[1]VisitInfo{.{.regex = self, .kind = VisitKind.WAY_DOWN}});

        while(worklist.items.len > 0) {
            try worklist.ensureUnusedCapacity(2);
            // only do this after enough capacity for at least two more items has been reserved, so that this pointer is not invalidated during appending
            var cur:*VisitInfo = &worklist.items[worklist.items.len - 1];

            // should never have a leaf/char in the worklist
            assert(cur.regex.isOperator(), "worklist contained leaf/char", .{});
            const left = cur.regex.left.?;

            switch(cur.kind){
                VisitKind.WAY_DOWN => {
                    // ensure we're constructing a post order traversal on the way down

                    // prepare next visit
                    defer cur.kind = VisitKind.WAY_UP;

                    if(left.isOperator())
                        worklist.appendAssumeCapacity(.{.regex = left, .kind = VisitKind.WAY_DOWN});

                    if(cur.regex.right) |right| if (right.isOperator())
                        worklist.appendAssumeCapacity(.{.regex = right, .kind = VisitKind.WAY_DOWN});

                    // if we haven't appended anything now, we will visit 'ourselves' immediately again, so we start the way up on this path
                },
                VisitKind.WAY_UP => {
                    // do all of the actual processing only on the way up
                    defer _ = worklist.pop(); // remove the current item from the worklist after dealing with it

                    // we can check whether left/right have a start/end state yet to determine whether we can just connect them, or we need to create a new start/end state (+transitions)

                    // TODO this can be optimized, we don't need a new start/end state in every case. But it does not save huge amounts of time, we will just have a bunch of unused states in the nfa, that won't be added to the dfa, because they're never reached from the start state
                    try nfa.addStates(2);
                    cur.regex.nfaStartState = nfa.numStates - 2;
                    const curStartState = cur.regex.nfaStartState.?;
                    cur.regex.nfaEndState = nfa.numStates - 1;
                    const curEndState = cur.regex.nfaEndState.?;

                    // in the operator, connect the start/end states of the operands with the operator
                    switch(cur.regex.kind){
                        Token.Kind.Union => {
                            const right = cur.regex.right.?;

                            if(!left.isOperator()){
                                try nfa.addTransition(curStartState, left.char, curEndState);
                            }else{
                                // if it is an operator, we have visited it before, so it has a start/end state, so we can just connect it
                                try nfa.addTransition(left.nfaEndState.?, null, curEndState);

                                // also connect the start state of the operator with the start state of the left operand
                                try nfa.addTransition(curStartState, null, left.nfaStartState.?);
                            }

                            if(!right.isOperator()){
                                try nfa.addTransition(curStartState, right.char, curEndState);
                            }else{
                                // same as left
                                try nfa.addTransition(right.nfaEndState.?, null, curEndState);
                                try nfa.addTransition(curStartState, null, right.nfaStartState.?);
                            }
                            // sidenote: see? this is exactly why ever programming language needs the ability to use 'local functions'/lambdas for readability. Do you hear me, Zig? :. Don't even need to be real functions in the end, can just inline all of them (and forbid non-inlinable ones)
                        },
                        Token.Kind.Concat => {
                            const right = cur.regex.right.?;

                            if(left.isOperator() and right.isOperator()){
                                // if both are operators, we have visited them before, so they have start/end states, so we can just connect them
                                try nfa.addTransition(left.nfaEndState.?, null, right.nfaStartState.?);
                                // and set the start/end of this operator to the start/end of the operands
                                cur.regex.nfaStartState = left.nfaStartState.?;
                                cur.regex.nfaEndState = right.nfaEndState.?;
                            }else if(left.isOperator()){
                                // if only left is an operator, we can take the existing end state of left and connect it with the char of right to the new end state
                                try nfa.addTransition(left.nfaEndState.?, right.char, curEndState);
                                cur.regex.nfaStartState = left.nfaStartState.?;
                            }else if(right.isOperator()){
                                // same as left
                                try nfa.addTransition(curStartState, left.char, right.nfaStartState.?);
                                cur.regex.nfaEndState = right.nfaEndState.?;
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
                                try nfa.addTransition(left.nfaEndState.?, null, left.nfaStartState.?);
                                cur.regex.nfaStartState = left.nfaStartState.?;
                                cur.regex.nfaEndState = left.nfaEndState.?;

                                // also connect the start state with the end state, to be able to match the empty string by skipping the sequence of states entirley
                                try nfa.addTransition(left.nfaStartState.?, null, left.nfaEndState.?);
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

        nfa.startState = self.nfaStartState.?;
        try nfa.designateStatesFinal(&[1]u32{self.nfaEndState.?});


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

// alphabet is implicitly the space of u8.
// passing an arena allocator and *not* calling deinit on the DFA, just on the arena is recommended. If you need to use another allocator, call deinit on the DFA directly
const RegExDFA = struct{
    const Transition                  = Tuple(&[_]type{u8, u32});
    const EntireTransitionMapOfAState = ArraySet(Transition, keyCompare(Transition, makeOrder(u8)));
    const UniqueStateSet              = ArraySet(u32, makeOrder(u32));

    const defaultTransitionCapacityForState = 2;

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    // an insert-first-lookup-later sorted vector like map would be preferable here for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends), but this will do for now
    transitions:[]EntireTransitionMapOfAState,
    finalStates:UniqueStateSet,

    internalAllocator:Allocator,

    pub fn init(allocer:Allocator) !@This() {
        return RegExDFA{
            .startState  = 0,
            .numStates   = 0,
            .transitions = try allocer.alloc(EntireTransitionMapOfAState, 0),
            .finalStates = try UniqueStateSet.init(allocer),
            .internalAllocator = allocer,
        };
    }
    
    pub fn deinit(self:@This()) void {
        for (self.transitions) |transitionsOfState| {
            transitionsOfState.deinit();
        }
        self.internalAllocator.free(self.transitions);
        self.finalStates.deinit();
    }

    pub fn addState(self:*@This()) !u32{
        try self.addStates(1);
        return self.numStates - 1;
    }

    pub fn addStates(self:*@This(), comptime n:comptime_int) !void{
        self.numStates += n;
        self.transitions = try self.internalAllocator.realloc(self.transitions, self.numStates);
        for(self.numStates-n..self.numStates) |i| {
            self.transitions[i] = try EntireTransitionMapOfAState.initCapacity(self.internalAllocator, defaultTransitionCapacityForState);
        }
    }

    pub fn designateStatesFinal(self:*@This(), states:[]const u32) !void{
        try self.finalStates.ensureUnusedCapacity(states.len);
        for (states) |state| {
            self.finalStates.insert(state, .{.AssumeCapacity = true}) catch unreachable;
        }
    }


    pub fn isInLanguage(self:@This(), word:[]const u8) bool{
        var curState:u32 = self.startState;
        for(word) |c| {
            curState = self.transitions[curState].findByKey(c) orelse return false;
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
                    for(dfa.transitions[curState].items) |transition| {
                        try writer.print("n{} -> n{}[label=\"{c}\"]; ", .{curState, transition[1], transition[0]});
                    }
                },
                FiniteAutomaton.nfa => |nfa| {
                    if(curState > nfa.transitions.len)
                        continue;

                    // could also put the same transitions on the same edge, reduce clutter a bit, but this is only for debugging anyway
                    for(nfa.transitions[curState].items) |transitions| {
                        for(transitions[1].items) |targetState| {
                            if(transitions[0]) |c| {
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

// alphabet is implicitly the space of u8.
// passing an arena allocator and *not* calling deinit on the NFA, just on the arena is recommended. If you need to use another allocator, call deinit on the NFA directly
const RegExNFA = struct {
    const UniqueStateSet = ArraySet(u32, makeOrder(u32));
    const EpsTransitionsForOneTerminal = Tuple(&[_]type{?u8, UniqueStateSet});
    const NonEpsTransitionsForOneTerminal = Tuple(&[_]type{u8, UniqueStateSet});

    // an insert-first-lookup-later sorted vector like map would be preferable here for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends), but this will do for now
    //const TransitionsOfAState = std.AutoHashMap(?u8, std.ArrayList(u32)); // ?u8 for eps transitions
    const EntireTransitionMapOfAState = ArraySet(EpsTransitionsForOneTerminal, keyCompare(EpsTransitionsForOneTerminal, struct {
        pub fn f(a:?u8, b:?u8) Order {
            // i hope this gets compiled into something proper...
            if(a == null){
                if(b == null)
                    return Order.eq;
                return Order.lt;
            }else if(b == null){
                return Order.gt;
            }
            return std.math.order(a.?,b.?);
        }
    }.f)); // ?u8 for eps transitions
    const FinalStates = UniqueStateSet;

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    transitions:[]EntireTransitionMapOfAState,
    finalStates:FinalStates, 

    internalAllocator:Allocator,

    pub fn init(allocer:Allocator) !@This() {
        var nfa                = RegExNFA{
            .startState        = 0,
            .numStates         = 0,
            .transitions       = try allocer.alloc(EntireTransitionMapOfAState, 0),
            .finalStates       = try FinalStates.init(allocer),
            .internalAllocator = allocer,
        };
        return nfa;
    }

    pub fn deinit(self:@This()) void {
        for (self.transitions) |transitionsOfState| {
            for(transitionsOfState.items) |transition| {
                transition[1].deinit();
            }
            transitionsOfState.deinit();
        }
        self.internalAllocator.free(self.transitions);
        self.finalStates.deinit();
    }

    pub fn addState(self:*@This()) !u32{
        try self.addStates(1);
        return self.numStates - 1;
    }

    pub fn addStates(self:*@This(), comptime n:comptime_int) !void{
        self.numStates += n;
        self.transitions = try self.internalAllocator.realloc(self.transitions, self.numStates);
        for(self.numStates-n..self.numStates) |i| {
            self.transitions[i] = try EntireTransitionMapOfAState.init(self.internalAllocator);
        }
    }

    pub fn designateStatesFinal(self:*@This(), states:[]const u32) !void{
        try self.finalStates.ensureUnusedCapacity(states.len);
        for (states) |state| {
            self.finalStates.insert(state, .{.AssumeCapacity = true}) catch unreachable;
        }
    }

    pub fn addTransition(self:*@This(), from:u32, with:?u8, to:u32) !void {
        _ = try self. addTransitionGetInfo(from, with, to);
    }


    // returns whether it added anything
    pub fn addTransitionGetInfo(self:*@This(), from:u32, with:?u8, to:u32) !bool {
        var entry = try self.transitions[from].findSpot(.{with, undefined}, .{.MakeSpaceForNewIfNotFound = true});
        if(!entry.found_existing){
            // set the char, if its new
            entry.item_ptr.*[0] = with;
            entry.item_ptr.*[1] = try UniqueStateSet.initElements(self.internalAllocator, &[1]u32{to});
            return true;
        }else{
            return !(try entry.item_ptr.*[1].insertAndGet(to, .{})).found_existing;
        }
    }

    // returns whether it added anything
    pub fn addAllTransitionsFromOtherState(self:*@This(), to:u32, from:u32, comptime opts:struct{excludeEpsilonTransitions:bool = false}) !bool {
        if(to == from)
            return false; 

        var addedSomething = false;
        const transitionsToCopyFrom:EntireTransitionMapOfAState = self.transitions[from];
        const transitionsToCopyTo:*EntireTransitionMapOfAState = &self.transitions[to];
        for(transitionsToCopyFrom.items) |transition| {
            const terminal = transition[0];
            if(opts.excludeEpsilonTransitions and terminal == null)
                continue;

            const transitionTargets = transition[1];
            
            const transitionsUsingTerminalFromStateToCopyTo = try transitionsToCopyTo.findSpot(.{terminal, undefined}, .{.MakeSpaceForNewIfNotFound = true});
            const targetListToChangePtr:*UniqueStateSet = &transitionsUsingTerminalFromStateToCopyTo.item_ptr.*[1];

            if(transitionsUsingTerminalFromStateToCopyTo.found_existing){
                const lengthBefore = targetListToChangePtr.items.len;
                // if the terminal already exists, just add all the targets to the existing set
                try targetListToChangePtr.addAll(transitionTargets);

                // can't just OR it, zig won't let me :(
                if(targetListToChangePtr.items.len != lengthBefore)
                    addedSomething = true;
            }else{
                // otherwise, create a new transition list
                transitionsUsingTerminalFromStateToCopyTo.item_ptr.*[0] = terminal;
                targetListToChangePtr.* = try transitionTargets.clone();
                addedSomething = true;
            }
        }
        return addedSomething;
    }

    // does not eliminate, but 'fill' epsilon transitions, so that they can be ignored from now on (because the language of the NFA after this function is the same with or without them)
    pub fn backUpEpsTransitions(self:*@This()) !void {
        // TODO this is obviously very inefficient, I'm thinking about how to do it better, maybe a kind of modifierd post order traversal (that takes cycles into consideration)

        // to handle transitive epsilons: just do this as long as it adds anything (this is why its inefficient)
        var changedSmth = true;
        while(changedSmth){
            changedSmth = false;
            for(0.., self.transitions) |state,*transitionsFromState| {
                if(transitionsFromState.findByKey(null)) |epsTargetsFromState| {
                    // solution: copy all transitions of the targeted states (epsTargetsFromState) to the current state
                    // also if the target is a final state, make this one final too
                    for(epsTargetsFromState.items) |epsTargetState|{
                        // exclude eps transitions here, they just make the whole thing bigger, and adding them anywhere might modify the epsTargetsFromState while we're iterating over them.
                        if(try self.addAllTransitionsFromOtherState(@intCast(state), epsTargetState, .{.excludeEpsilonTransitions = true}))
                            changedSmth = true;

                        // make final if target is final
                        if(self.finalStates.contains(epsTargetState)){
                            if(!self.finalStates.contains(@intCast(state))){
                                try self.designateStatesFinal(&[1]u32{@truncate(state)});
                                changedSmth = true;
                            }
                        }
                    }
                }
            }
        }
    }

    // this function assumes backUpEpsTransitions has been called just before!
    // this also deinitializes the NFA, so it can't be used afterwards
    // TODO handle different allocator for DFA, currently that just does malloc
    pub fn toPowersetConstructedDFA(self:*@This()) !RegExDFA{
        // combine all transitions into new states (if they don't exist yet), add them to the worklist

        // maps input slice of nfa states to dfa state
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
        
        var dfa = try RegExDFA.init(self.internalAllocator);
        // worklist of nfa (and generated i.e. powerset-) states to visit
        var worklist = try std.ArrayList(UniqueStateSet).initCapacity(self.internalAllocator, 8);

        // add start state to new DFA
        dfa.startState = try dfa.addState();
        var startStateSet = try UniqueStateSet.initElements(self.internalAllocator, &[1]u32{self.startState});
        try nfaToDfaStates.putNoClobber(startStateSet.items, dfa.startState);

        // used like a stack
        try worklist.append(startStateSet);

        // TODO 'curNfaState(s)' is not named perfectly, because it can also be a 'powerset state' that doesnt exist in the original NFA, just implicitly
        while(worklist.popOrNull()) |curNfaStates| {
            // get the state, has to be in there (but not visited yet) if its in the worklist
            const curDfaState = nfaToDfaStates.get(curNfaStates.items).?;

            // if any of the current nfa states is final, make the dfa state final
            loop: for(curNfaStates.items) |curNfaState| {
                if(self.finalStates.contains(curNfaState)){
                    try dfa.designateStatesFinal(&[1]u32{@truncate(curDfaState)});
                    break :loop;
                }
            }

            // then go through the transitions of the states, and construct a transition map for the state step by step
            // after the transition map is complete, the actual dfa states can be created and the dfa transitions can be added
            var combinedTransitionsForCurNfaState = try ArraySet(NonEpsTransitionsForOneTerminal, keyCompare(NonEpsTransitionsForOneTerminal, makeOrder(u8))).init(self.internalAllocator);
            // the transition lists in here are kept sorted, for deduplication (as they represent sets)

            for(curNfaStates.items) |curNfaState| {
                assert(self.transitions.len > curNfaState, "nfa state out of bounds, nfa is invalid", .{});

                for(self.transitions[curNfaState].items) |*transition| {
                    // ignore empty, because eps transitions are already handled

                    if(transition.*[0]) |c| {
                        // first: find/insert the transition map for the current char
                        // results are still correct
                        var entry = try combinedTransitionsForCurNfaState.findSpot(.{c, undefined}, .{.MakeSpaceForNewIfNotFound = true});
                        // either create, if it doesn't exist yet or add all
                        if(!entry.found_existing){
                            // set the char
                            entry.item_ptr.*[0] = c;
                            entry.item_ptr.*[1] = try transition.*[1].clone();
                        }else{
                            try entry.item_ptr.*[1].addAll(transition.*[1]);
                        }
                    }
                }
            }

            // now we have the combined transitions for the current state, so we can create the actual states and add the transitions in the dfa

            for(combinedTransitionsForCurNfaState.items) |transition| {
                // create or get state
                var targetStateEntry = try nfaToDfaStates.getOrPut(transition[1].items);
                if(!targetStateEntry.found_existing){
                    targetStateEntry.value_ptr.* = try dfa.addState();

                    // add (the possibly combined state of the nfa) to worklist, because its new -> we haven't visited it yet
                    try worklist.append(transition[1]);
                }

                // add transition
                try dfa.transitions[curDfaState].insert(.{transition[0], targetStateEntry.value_ptr.*}, .{});
            }

        }

        // TODO when the arena allocator works call deinit etc.

        return dfa;
    }
};

const expect = std.testing.expect;

test "tokenizer" {
    const input = "xyz|w*(abc)*de*f";
    var tok = try Tokenizer.init(input, std.testing.allocator);
    defer tok.deinit();
    const buf = try tok.debugFmt();
    try expect(std.mem.eql(u8, buf.items, "x y z|w* (a b c)* d e* f"));
}

test "ab* DFA" {
    var dfa = try RegExDFA.init(std.testing.allocator);
    defer dfa.deinit();

    try dfa.addStates(2);
    const a = 0;
    const b = 1;

    try dfa.transitions[a].insert(.{'a', b}, .{});
    try dfa.transitions[b].insert(.{'b', b}, .{});
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
    var nfa = try RegExNFA.init(std.testing.allocator);
    defer nfa.deinit();

    try nfa.addStates(6);
    try nfa.addTransition(0, 'a', 1);
    try expect(nfa.transitions[0].findByKey('a') != null);
    try expect(nfa.transitions[0].findByKey('a').?.items[0] == 1);
    try expect(nfa.transitions[0].items[0][1].items[0] == 1);
    try expect(nfa.transitions[0].findByKey('b') == null);

    try nfa.addTransition(0, 'a', 2);
    try nfa.addTransition(1, 'b', 3);
    try nfa.addTransition(2, 'a', 4);
    try nfa.addTransition(4, 'a', 5);
    try nfa.designateStatesFinal(&[_]u32{3,5});

    try expect(std.mem.eql(u32, nfa.transitions[0].findByKey('a').?.items, &[2]u32{1,2}));
}

test "NFA eps removal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(2);
    try nfa.addTransition(0, null, 1);
    try nfa.addTransition(1, 'a', 1);
    try nfa.designateStatesFinal(&[_]u32{1});

    try expect(!nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].findByKey('a') == null);

    try nfa.backUpEpsTransitions();

    try expect(nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].findByKey('a') != null);
    try expect((nfa.transitions[0].findByKey('a').?).items[0] == 1);
}

test "NFA transitive eps removal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(3);
    try nfa.addTransition(0, null, 1);
    try nfa.addTransition(1, null, 2);
    try nfa.addTransition(2, 'a', 2);
    try nfa.designateStatesFinal(&[_]u32{2});

    try expect(!nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].findByKey('a') == null);

    try nfa.backUpEpsTransitions();

    try expect(nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].findByKey('a').?.items[0] == 2);
}

test "NFA simple powerset construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
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
}

test "regex to dfa" {
    const input = "xyz|w*(abc)*de*f";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var tok = try Tokenizer.init(input, arena.allocator());
    defer tok.deinit();
    const regex = try RegEx.parseExpr(arena.allocator(), 0, &tok);
    assert(!tok.hasNext(), "expected EOF, but there were tokens left", .{});

    var dfa = try regex.toDFA();

    try expect(dfa.isInLanguage("xyz"));

    try expect(!dfa.isInLanguage("xz"));
    try expect(!dfa.isInLanguage("xy"));
    try expect(!dfa.isInLanguage("x"));
    try expect(!dfa.isInLanguage("y"));
    try expect(!dfa.isInLanguage("z"));

    try expect(dfa.isInLanguage("wwwwwwwwdf"));
    try expect(dfa.isInLanguage("df"));
    try expect(dfa.isInLanguage("deef"));
    try expect(dfa.isInLanguage("wabcabcdeeef"));
    try expect(dfa.isInLanguage("wwwwabcabcabcdeeef"));

    try expect(!dfa.isInLanguage("wwwwacabcabcdeeef"));
    try expect(!dfa.isInLanguage("xyz" ++ "wwwwwwwwdf"));
    try expect(!dfa.isInLanguage("xyz" ++ "df"));
    try expect(!dfa.isInLanguage("xyz" ++ "wabcabcdeeef"));
    try expect(!dfa.isInLanguage("xyz" ++ "wwwwabcabcabcdeeef"));
}

pub fn main() !void {
    const writer = std.io.getStdOut().writer();

    const input = "xyz|w*(abc)*de*f";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var tok = try Tokenizer.init(input, arena.allocator());
    defer tok.deinit();
    const regex = try RegEx.parseExpr(0, &tok);
    assert(!tok.hasNext(), "expected EOF, but there were tokens left", .{});

    var dfa = try regex.toDFA();
    const fa = FiniteAutomaton{.dfa = &dfa};

    try fa.printDOT(writer);
}
