const std = @import("std");
const cAllocer = std.heap.c_allocator;
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
fn structFieldType(comptime T:type, comptime fieldIndex:comptime_int) type{
    return @typeInfo(T).Struct.fields[fieldIndex].type;
}

test "semantically analyze relevant types without explicit calls" {
    std.testing.refAllDeclsRecursive(RegEx);
    std.testing.refAllDeclsRecursive(RegExDFA);
    std.testing.refAllDeclsRecursive(RegExNFA);
    // doesn't use a simple u32 array set, because that includes methods that assume a key-value type store, and thus consciously don't pass semantic analysis in some cases.
    std.testing.refAllDeclsRecursive(ArraySet(Pair(u32, u32), keyCompare(Pair(u32, u32), makeOrder(u32))));
    std.testing.refAllDeclsRecursive(UnionFind(u32, makeOrder(u32)));
    std.testing.refAllDeclsRecursive(RangeMap(u32, makeOrder(u32), u32));
}

fn isOk(errUnionType: anytype) bool {
    _ = errUnionType catch return false;
    return true;
}

fn isErr(errUnionType: anytype) bool {
    return !isOk(errUnionType);
}

const expect          = std.testing.expect;
const expectEqual     = std.testing.expectEqual;
const expectEqualDeep = std.testing.expectEqualDeep;
const expectError     = std.testing.expectError;

fn expectAnyError(value:anytype) !void {
    _ = value catch {
        return;
    };
    try expect(false);
}

// unwraps the parser result, and checks that the diag contains the expected error
fn expectParserError(expectedError: anyerror, parserResult: anytype) !void {
    const diag:Diag = parserResult[1];
    defer diag.deinit();
    for(diag.msgs.items) |msg| {
        if(msg.kind.Error == expectedError)
            return;
    }
    try expectAnyError(parserResult[0]);
}

// unwraps the optional and std.testing.expect's that its not null (similar to just doing .?, but with an explicit expect)
fn expectNotNull(value:anytype) !@typeInfo(@TypeOf(value)).Optional.child {
    try expect(value != null);
    return value.?;
}

fn expectOrSkip(condition:bool) !void{
    if(!condition)
        return error.SkipZigTest;
}

const Tuple = std.meta.Tuple;
fn Pair(comptime T:type, comptime U:type) type {
    return Tuple(&[2]type{T, U});
}
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

const Termcolor = struct{
    const Reset = "\x1b[0m";
    // use the defaults from GCC
    const Error = "\x1b[01;31m";
    const Warning = "\x1b[01;35m";
};

// sorted array set. Should not be used if removal is important, try to treat it as an insert-only set
// an insert-first-lookup-later sorted vector like map for performance (like https://www.llvm.org/docs/ProgrammersManual.html recommends)
pub fn ArraySet(comptime T:type, comptime comparatorFn:(fn (T, T) Order)) type {
    return struct {
        const Item = T;

        items:[]T,
        internalAllocator:Allocator,
        internalSlice:[]T,

        const InsertOpts = struct{
            ReplaceExisting:bool       = false, // important for example if this is a key/value map and comparator fn only compares the key
            AssumeCapacity:bool        = false,
            LinearInsertionSearch:bool = false,
            // TODO should maybe be 'JustAppendDontSort'
            DontSort:bool              = false,
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

            const findResults = try self.findOrMakeSpot(itemToInsert, .{.AssumeCapacity = opts.AssumeCapacity, .LinearInsertionSearch = opts.LinearInsertionSearch});
            // if we didnt find it, or we should replace it, write to it
            if(!findResults.found_existing or opts.ReplaceExisting)
                findResults.item_ptr.* = itemToInsert;

            // results are still correct
            return findResults;
        }

        // TODO would be great if this supported merging at some point, could parameterize it with 'shouldMerge' and 'merge' functions passed to this one
        // invalidates pointers and capacity guarantees in all cases (!)
        // this could also be done sort of in-place with sufficient guarantees, but that is unnecessarily complex for now
        pub fn addAll(a:*@This(), b:@This()) Allocator.Error!void {
            if(a.items.ptr == b.items.ptr){
                assert(a.items.len == b.items.len, "addAll called on the same set with different lengths", .{});
                return;
            }else if(b.items.len == 0){
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
        pub fn remove(self:*@This(), itemToRemove:T, comptime findOpts:struct{LinearInsertionSearch:bool = false}) bool {
            const spot = self.findSpot(itemToRemove, .{.LinearInsertionSearch = findOpts.LinearInsertionSearch}) orelse return false;
            if(spot.found_existing){
                const i = (@intFromPtr(spot.item_ptr) - @intFromPtr(self.items.ptr))/@sizeOf(T);
                std.mem.copyForwards(T, self.items[i..self.items.len-1], self.items[i+1..self.items.len]);
                self.items.len -= 1;
                return true;
            }
            return false;
        }

        // returns whether the set contains the item finds the item using binary search
        pub fn contains(self:*const @This(), itemToFind:T) bool {
            const spot = self.findSpot(itemToFind, .{.LinearInsertionSearch = false}) orelse return false;
            return spot.found_existing;
        }

        pub fn containsKey(self:*const @This(), keyToFind:@typeInfo(T).Struct.fields[0].type) bool {
            return self.contains(.{keyToFind, undefined});
        }

        // finds the value of the first item that has a key greater than or equal to the key to compare against. If there is no greater or equal key, null is returned.
        pub fn findByKey(self:*const @This(), keyToCompareAgainst:structFieldType(T, 0)) ?structFieldType(T, 1){
            if(@typeInfo(T).Struct.fields.len != 2)
                @compileError("findByKey only works when this set is being used as a key value map, i.e. with two-long tuple elements");

            const spot = self.findSpot(.{keyToCompareAgainst, undefined}, .{.LinearInsertionSearch = false}) orelse return null;
            return if(spot.found_existing) spot.item_ptr.*[1] else null;
        }

        // finds the first item that is greater than or equal to the item to find. If there is no greater or equal item, null is returned. If item_ptr.* is greater, found_existing is false. Otherwise, found_existing is true
        pub fn findSpot(self:*const @This(), itemToCompareAgainst:T, comptime opts:struct{
            LinearInsertionSearch:bool = false,
        }) ?SpotInfo {
            // can confidently @constCast, and ignore the error, because we don't modify anything (guaranteed by the implementation)
            return @constCast(self).findSpotInternal(itemToCompareAgainst, .{.LinearInsertionSearch = opts.LinearInsertionSearch}) catch unreachable;
        }

        // finds the spot of the item that is equal to the item to find, or the spot where it should be inserted if it does not exist (expanding the array, possibly allocating new space)
        pub fn findOrMakeSpot(self:*@This(), itemToCompareAgainst:T, comptime opts:struct{
            AssumeCapacity:bool        = false,
            LinearInsertionSearch:bool = false,
        }) !SpotInfo {
            return (try self.findSpotInternal(itemToCompareAgainst, .{.MakeSpaceForNewIfNotFound = true, .AssumeCapacity = opts.AssumeCapacity, .LinearInsertionSearch = opts.LinearInsertionSearch})) orelse unreachable; // cannot be null, because we make space if it doesnt exist
        }

        // only use this if you know what you're doing, try to use `contains`, the other `find...` function or `insert` if possible
        // finds the first item that is greater than or equal to the item to find and returns a pointer to it or the place it should be inserted if it does not exist, as well as whether or not it exists
        // if opts.MakeSpaceForNewIfNotFound is set, the array will be expanded and the returned pointer will point to the new item (undefined) item.
        // if opts.MakeSpaceForNewIfNotFound is not set and .found_existing is false, the returned pointer is null, if the array contains no element greater than the passed element, and valid if there is such an element.
        //   can not return an error if opts.MakeSpaceForNewIfNotFound is not set
        fn findSpotInternal(self:*@This(), itemToCompareAgainst:T, comptime opts:struct{
            MakeSpaceForNewIfNotFound:bool = false,
            AssumeCapacity:bool            = false,
            LinearInsertionSearch:bool     = false,
        }) !?SpotInfo {
            if(!opts.MakeSpaceForNewIfNotFound and opts.AssumeCapacity)
                @compileError("Can't assume capacity if findSpotInternal can not insert");

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
                try self.insertBeforeInternal(firstGreater, opts.AssumeCapacity);
            }else {
                if(firstGreater == self.items.len) 
                    // in this case, we don't want to return an invalid pointer, so we return null (as the whole spot info, because found existing is obviously implicitly false in this case), as the pointer would not make sense, if the array has not been expanded
                    return null;
            }

            return .{.item_ptr = @ptrCast(self.items.ptr + firstGreater), .found_existing = false};
        }

        // do not use this function to simply insert an element, this can only be used if you have found the proper insertion point already
        fn insertBeforeInternal(self:*@This(), index:usize, assumeCapacity:bool) Allocator.Error!void {
            if(!assumeCapacity)
                try self.ensureUnusedCapacity(1);

            // let the `items` slice know that it has grown
            self.items.len += 1;

            // shift everything to the right
            std.mem.copyBackwards(T, self.internalSlice[index+1..], self.internalSlice[index..(self.items.len - 1)]); // -1: old item length
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
fn keyCompare(comptime T:type, comptime compare:fn(structFieldType(T, 0), structFieldType(T, 0)) Order) fn(T, T) Order {
    return struct {
        pub fn f(a:T, b:T) Order {
            return compare(a[0], b[0]);
        }
    }.f;
}

test "array set" {
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
        const rand1 = rnd.random().intRangeLessThan(u32, 0, 1000);
        const rand2 = rnd.random().intRangeLessThan(u32, 0, 1000);

        try set1.insert(rand1, insertionOpts);
        try set2.insert(rand2, insertionOpts);

        try correctSet.insert(rand1, insertionOpts);
        try correctSet.insert(rand2, insertionOpts);

        try set1.addAll(set2);

        if(!std.mem.eql(u32, set1.items, correctSet.items)){
            set1.debugPrint();
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

pub fn UnionFind(comptime T:type, comptime comparatorFn:(fn (T, T) Order)) type {
    return struct{
        parent:ArraySet(Tuple(&[2]type{T, T}), keyCompare(Tuple(&[2]type{T, T}), comparatorFn)),

        pub fn init(allocator:Allocator) !@This() {
            return @This(){
                .parent = try ArraySet(Tuple(&[2]type{T, T}), keyCompare(Tuple(&[2]type{T, T}), comparatorFn)).init(allocator),
            };
        }

        pub fn deinit(self:@This()) void {
            self.parent.deinit();
        }

        pub fn find(self:*@This(), item:T) !*T {
            const parent = try self.parent.findOrMakeSpot(.{item, undefined}, .{});
            // smallest sets are simply one-element sets represented by themselves. These get inserted explicitly, so that a union (yunyin) can be done with them
            if(!parent.found_existing){
                parent.item_ptr.*[0] = item;
                parent.item_ptr.*[1] = item;
                return &parent.item_ptr.*[1];
            }

            // parents that point to themselves are also the representative of their set
            if(comparatorFn(parent.item_ptr.*[1], item) == Order.eq)
                return &parent.item_ptr.*[1];

            const rep = try self.find(parent.item_ptr.*[1]);
            // path compression
            parent.item_ptr.*[1] = rep.*;
            return rep;
        }

        // representative of a is now the representative of all of a \cup b
        pub fn yunyin(self:*@This(), a:T, b:T) !void {
            const aParent = try self.find(a);
            const bParent = try self.find(b);

            if(comparatorFn(aParent.*, bParent.*) == Order.eq)
                return;

            bParent.* = aParent.*;
        }
    };
}

test "union-find" {
    const T = u32;
    var uf = try UnionFind(T, makeOrder(T)).init(std.testing.allocator);
    defer uf.deinit();

    try uf.yunyin(1, 2);
    try expect(try uf.find(1) == try uf.find(2));
    try expect((try uf.find(1)).* == 1);

    try uf.yunyin(3, 4);
    try expect(try uf.find(3) == try uf.find(4));
    try expect((try uf.find(3)).* == 3);

    try uf.yunyin(2, 4);
    try expect((try uf.find(1)).* == 1);
    for(1..5) |i| {
        try expect(try uf.find(@intCast(i)) == try uf.find(1));
    }
}

// ranges are inclusive and may not overlap (they are seen as disjoint sets)
pub fn RangeMap(comptime RangeableKey:type, comptime keyOrder:(fn(RangeableKey, RangeableKey) Order), comptime Value:type) type {
    return struct{
        // maps highest element of range to (lowest, value)
        const Item = Pair(RangeableKey, Pair(RangeableKey, Value));
        const Map = ArraySet(Item, keyCompare(Item, keyOrder));
        map:Map,
        
        pub fn init(allocator:Allocator) !@This() {
            return @This(){
                .map = try Map.init(allocator),
            };
        }

        pub fn initCapacity(allocator:Allocator, capacity:usize) Allocator.Error!@This() {
            return @This(){
                .map = try Map.initCapacity(allocator, capacity),
            };
        }

        // clones the set, uses the same allocator. Does not make any guarantees about the capacity of the new set, just that the actual elements are the same
        pub fn clone(self:@This()) !@This() {
            return @This(){
                .map = try self.map.clone(),
            };
        }

        pub fn deinit(self:@This()) void {
            self.map.deinit();
        }

        // inserts a range + value. ranges are inclusive and may not overlap
        pub fn insert(self:*@This(), lower:RangeableKey, upper:RangeableKey, value:Value, comptime opts:struct{AssumeNoOverlap:bool = false}) !void {
            _ = try self.insertAndGet(lower, upper, value, .{.AssumeNoOverlap = opts.AssumeNoOverlap});
        }

        // inserts a range + value. ranges are inclusive and may not overlap
        pub fn insertAndGet(self:*@This(), lower:RangeableKey, upper:RangeableKey, value:Value, comptime opts:struct{AssumeNoOverlap:bool = false}) !*Item {
            assert(keyOrder(lower, upper) != Order.gt, "lower bound of range must be <= than upper bound", .{});
            if(opts.AssumeNoOverlap){
                assert(self.find(lower) == null, "tried to insert existing range; ranges cannot overlap", .{});
                assert(self.find(upper) == null, "tried to insert existing range; ranges cannot overlap", .{});
            }else{
                if(self.find(lower) != null or self.find(upper) != null)
                    return error.OverlappingRanges;
            }
            return (try self.map.insertAndGet(.{upper, .{lower, value}}, .{})).item_ptr;
        }

        pub fn insertSingle(self:*@This(), key:RangeableKey, value:Value, comptime opts:struct{AssumeNoOverlap:bool = false}) !void {
            try self.insert(key, key, value, .{.AssumeNoOverlap = opts.AssumeNoOverlap});
        }

        pub fn find(self:*const @This(), key:RangeableKey) ?Value {
            return (self.findByPtr(key) orelse return null).*;
        }

        pub fn findByPtr(self:*const @This(), key:RangeableKey) ?*Value {
            return &(self.findItem(key) orelse return null).*[1][1];
        }

        pub fn findItem(self:*const @This(), key:RangeableKey) ?*Item {
            // the inner self.map method finds the first greater than or equal to key -> will be the highest element of the range that could contain key, if key >= lowest
            const spotInfo = self.map.findSpot(.{key, undefined}, .{}) 
                // passed key is higher than any highest element of a range
                orelse return null;

            if(keyOrder(key, spotInfo.item_ptr.*[1][0]) != Order.lt)
                // lies within the range
                return spotInfo.item_ptr;

            return null;
        }

        const SpotInfo = struct{item_ptr:*Item, found_existing:bool, 
            fn setRange(self:*@This(), newLower:RangeableKey, newUpper:RangeableKey) void { self.item_ptr.*[0] = newUpper; self.item_ptr.*[1][0] = newLower; }
            fn getRange(self:*const @This()) Pair(RangeableKey, RangeableKey) { return .{self.item_ptr.*[0], self.item_ptr.*[1][0]}; }
            fn value(self:*@This()) *Value { return &self.item_ptr.*[1][1]; }
            fn lower(self:*@This()) *RangeableKey { return &self.item_ptr.*[1][0]; }
            fn upper(self:*@This()) *RangeableKey { return &self.item_ptr.*[0]; }
        };

        pub fn findOrMakeSpot(self:*@This(), key:RangeableKey, opts:struct{AssumeCapacity:bool = false}) !SpotInfo {
            // TODO unfortunately duplicates code from findSpotInternal, because to avoid searching twice, we need to make nuanced modifications to the search
            var left: usize = 0;
            var right: usize = self.map.items.len;

            // binary search, but we can't use the std.sort one, because we need to insert if not found
            // so just copy that one and change it :
            while (left < right) {
                // Avoid overflowing in the midpoint calculation
                const mid = left + (right - left) / 2;
                // Compare the key with the midpoint element
                switch(keyOrder(key, self.map.items[mid][0])){
                    Order.lt => right = mid,
                    Order.gt => left = mid + 1,
                    Order.eq => return .{.item_ptr = &self.map.items[mid], .found_existing = true},
                }
            }
            assert(left == right, "after binary search to insert, we should be left with a definitive insertion point", .{});
            // left again points to first element that is greater than the item to insert -> insert before that

            const firstGreater = left;
            // assert sensible insertion point
            assert(firstGreater <= self.map.items.len, "Find reached too far outside the array", .{});

            // DIFFERENCE: check if the key lies in the found range, just return it
            if(firstGreater < self.map.items.len and keyOrder(key, self.map.items[firstGreater][1][0]) != Order.lt)
                return .{.item_ptr = @ptrCast(self.map.items.ptr + firstGreater), .found_existing = true};

            // otherwise insert:
            if(!opts.AssumeCapacity)
                try self.map.ensureUnusedCapacity(1);

            // let the `items` slice know that it has grown
            self.map.items.len += 1;

            // shift everything to the right
            std.mem.copyBackwards(Item, self.map.internalSlice[firstGreater+1..], self.map.internalSlice[firstGreater..(self.map.items.len - 1)]); // -1: old item length

            return .{.item_ptr = @ptrCast(self.map.items.ptr + firstGreater), .found_existing = false};
        }

        // simply accesses the internal slice by index (assumes the index exists). Only use if you understand the maps inner workings
        pub fn valueByIndex(self:*const @This(), index:usize) Value {
            return self.map.items[index][1][1];
        }
    };
}

test "range map"{
    var rm = try RangeMap(u32, makeOrder(u32), u32).init(std.testing.allocator); 
    defer rm.deinit();

    try rm.insert(0, 10, 1, .{});
    for(0..11) |i| {
        const ii = oldIntCast(i, u32);
        try expect(rm.find(@intCast(ii)).? == 1);
        try expectError(error.OverlappingRanges, rm.insert(ii, ii, 1, .{}));
    }

    try expectError(error.OverlappingRanges, rm.insert(0, 10, 1, .{}));
    try expectError(error.OverlappingRanges, rm.insert(3, 6, 1, .{}));
}

test "range map transitions" {
    // adapted from NFA
    const UniqueStateSet = ArraySet(u32, makeOrder(u32));

    const EntireTransitionMapOfAState = RangeMap(u8, makeOrder(u8), UniqueStateSet);

    var map = try EntireTransitionMapOfAState.init(std.testing.allocator);
    defer map.deinit();
    try map.insert('a', 'z', try UniqueStateSet.init(std.testing.allocator), .{});
    var res = try expectNotNull(map.findByPtr('a'));
    defer res.deinit();
    try res.insert(1, .{});
    res = try expectNotNull(map.findByPtr('a'));
    try expect(res.contains(1));
    res = try expectNotNull(map.findByPtr('a'));
    try res.insert(3, .{});
    res = try expectNotNull(map.findByPtr('a'));
    try expect(res.contains(3));
    res = try expectNotNull(map.findByPtr('a'));
    try res.insert(2, .{});
    res = try expectNotNull(map.findByPtr('a'));
    try expect(res.contains(2));

    for('a'..('z'+1)) |c|{
        var res2 = try expectNotNull(map.findByPtr(@intCast(c)));
        for(1..4) |i| {
            try expect(res2.contains(@intCast(i)));
        }
    }
}

pub fn formatTransitionChar(char:u8, writer: anytype) !void {
    // handle some special chars
    switch(char){
        0    => _ = try writer.write("&epsilon;"),
        ' '  => _ = try writer.write("\\s"),
        '\n' => _ = try writer.write("\\n"),
        '\t' => _ = try writer.write("\\t"),
        '\r' => _ = try writer.write("\\r"),
        else => {
            if(char < 0x20 or char >= 0xff){
                try writer.print("0x{x:0>2}", .{char});
            }else{
                try writer.writeByte(char);
            }
        }
    }
}

pub fn formatTransitionChars(chars:Pair(u8, u8), writer: anytype) !void {
    // TODO for correct DOT output, need to html string escape the chars at some point

    // single char transition
    if(chars[0] == chars[1]){
        try formatTransitionChar(chars[0], writer);
    } // anychar transition
    else if(chars[0] == 1 and chars[1] == 255){
        try writer.print("any", .{});
    } // range transition
    else{
        try formatTransitionChar(chars[0], writer);
        try writer.writeByte('-');
        try formatTransitionChar(chars[1], writer);
    }
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
        // syntactic sugar
        Plus,
        Question,
        RangeMinus,
        RangeInvert,
        LSquareBrack,
        RSquareBrack,

        // hope that the compiler knows that this is often used at comptime
        pub fn precedenceAndChar(self:@This()) struct{prec:u8, char:u8} {
            return switch(self){
                Kind.AnyChar      => .{.prec = 0, .char = '.'},
                Kind.Union        => .{.prec = 1, .char = '|'},
                Kind.Concat       => .{.prec = 2, .char = ' '},
                Kind.Kleen        => .{.prec = 3, .char = '*'},
                Kind.Plus         => .{.prec = 3, .char = '+'},
                Kind.Question     => .{.prec = 3, .char = '?'},
                Kind.LParen       => .{.prec = 0, .char = '('},
                Kind.RParen       => .{.prec = 0, .char = ')'},
                Kind.LSquareBrack => .{.prec = 0, .char = '['},
                // e.g. char, RangeInvert, RangeMinus
                else => .{.prec = 0, .char = 'x'},
            };
        }

        pub fn fromChar(theChar:u8) @This() {
            // this seems to get compiled into smth proper
            return switch(theChar){
                Kind.AnyChar.precedenceAndChar().char      => Kind.AnyChar,
                Kind.Union.precedenceAndChar().char        => Kind.Union,
                Kind.Kleen.precedenceAndChar().char        => Kind.Kleen,
                Kind.Plus.precedenceAndChar().char         => Kind.Plus,
                Kind.Question.precedenceAndChar().char     => Kind.Question,
                Kind.LParen.precedenceAndChar().char       => Kind.LParen,
                Kind.RParen.precedenceAndChar().char       => Kind.RParen,
                Kind.LSquareBrack.precedenceAndChar().char => Kind.LSquareBrack,
                else                                       => Kind.Char
            };
        }

        pub fn fromCharInsideCharRangeGroup(theChar:u8) @This() {
            // this seems to get compiled into smth proper
            return switch(theChar){
                '^' => Kind.RangeInvert,
                '-' => Kind.RangeMinus,
                // rsquarebrack is only a special char inside a char range group
                ']' => Kind.RSquareBrack,
                // inside a char range group, a period is a literal char
                '.' => Kind.Char,
                else => fromChar(theChar)
            };
        }

        pub fn canConcatToRight(self:@This()) bool {
            return switch(self){
                Kind.Char         => true,
                Kind.AnyChar      => true,
                Kind.Kleen        => true,
                Kind.Plus         => true,
                Kind.Question     => true,
                Kind.RParen       => true,
                Kind.RSquareBrack => true,
                else              => false
            };
        }
        pub fn canConcatToLeft(self:@This()) bool {
            return switch(self){
                Kind.Char         => true,
                Kind.AnyChar      => true,
                Kind.LParen       => true,
                Kind.LSquareBrack => true,
                else              => false
            };
        }
    };

    pub fn initChar(char:u8) @This() {
        return Token{
            .kind = Token.Kind.fromChar(char),
            .char = char
        };
    }

    pub fn initCharInsideCharRangeGroup(char:u8) @This() {
        return Token{
            .kind = Token.Kind.fromCharInsideCharRangeGroup(char),
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

const SyntaxError = error{InvalidToken, PrematureEnd};
const ParseError = error{OutOfMemory, RootExpressionInvalid, SemanticallyInvalidRange} || SyntaxError;
const CompileError = ParseError;

const Diag =  struct{
    msgs:std.ArrayList(Msg),

    const Msg = struct{
        const Kind = union(enum) {
            Error:CompileError,
            Warning:void,
        };
        kind:Kind,
        // inclusive start exclusive end, index into source
        location:Pair(u32, u32),
        str:[]const u8,
    };

    pub fn init(allocator:Allocator) @This() {
        return @This(){
            .msgs = std.ArrayList(Msg).init(allocator),
        };
    }

    pub fn deinit(self:@This()) void {
        self.msgs.deinit();
    }

    pub fn registerError(self:*@This(), errorKind:CompileError, location:Pair(u32, u32), str:[]const u8) error{OutOfMemory}!void {
        try self.msgs.append(.{.kind = Msg.Kind{.Error = errorKind}, .location = location, .str = str});
    }

    pub fn throw(self:*@This(), errorKind:CompileError, location:Pair(u32, u32), str:[]const u8) CompileError!void {
        try self.register(errorKind, location, str);
        return errorKind;
    }

    pub fn warn(self:*@This(), location:Pair(u32, u32), str:[]const u8) error{OutOfMemory}!void {
        try self.msgs.append(.{.kind = Msg.Kind{.Warning = {}}, .location = location, .str = str});
    }

    pub fn printAll(self:*const @This(), writer:anytype, source:[]const u8) !void {
        for (self.msgs.items) |msg| {
            // all messages print the message, the whole source string, and then highlight the location
            const start = msg.location[0];
            const startInside = @min(start, source.len -| 1);
            const end = msg.location[1];
            const endInside = @min(end, source.len -| 1);

            
            const errorColor, const errorName = switch(msg.kind){
                Msg.Kind.Error => .{Termcolor.Error, "Error"},
                Msg.Kind.Warning => .{Termcolor.Warning, "Warning"},
            };

            // these could all be one statement, but this is more readable

            try writer.print("{s}{s}: " ++ Termcolor.Reset ++ "{s}\n", .{errorColor, errorName, msg.str});

            try writer.print("{s}{s}{s}{s}{s}\n", .{source[0..startInside], errorColor, source[startInside..endInside], Termcolor.Reset, source[endInside..source.len]});
            
            try writer.writeByteNTimes(' ', start);
            try writer.print("{s}^", .{errorColor});
            try writer.writeByteNTimes('~', end-start-|1);
            try writer.print(Termcolor.Reset ++ "\n", .{} );
        }
    }
};

const Tokenizer = struct {
    tokens:[]Token,
    cur:u32,
    internalAllocator:Allocator,
    diag:*Diag,

    // can be used without Tokenizer, but tokenizer is more convenient
    fn tokenize(allocer:Allocator, input:[]const u8) error{OutOfMemory, PrematureEnd}![]Token {
        // we need to fill in concat tokens, as they are implicit in the input
        var tokens:[]Token = try allocer.alloc(Token, input.len << 1); // multiply by 2 to account for concat tokens
        errdefer allocer.free(tokens);
        var tokenI:u32 = 0;
        var inputI:u32 = 0;
        var isInCharGroupingSquareBrack = false;
        while(inputI < input.len) : (inputI += 1) {
            const char = input[inputI];

            var curTokenInit:Token = undefined;
            // escaping
            if(char == '\\'){
                inputI += 1;
                if(inputI >= input.len)
                    return SyntaxError.PrematureEnd;

                curTokenInit = Token{.char = input[inputI], .kind = Token.Kind.Char};
            }else if(isInCharGroupingSquareBrack){
                curTokenInit = Token.initCharInsideCharRangeGroup(char);
            }else{
                curTokenInit = Token.initChar(char);
            }
            
            // to make clear that its const from now on
            const curToken = curTokenInit;

            // hope this gets unrolled
            if(tokenI > 0 and curToken.kind.canConcatToLeft() and tokens[tokenI-1].kind.canConcatToRight() and !isInCharGroupingSquareBrack) {
                tokens[tokenI] = Token.initKind(Token.Kind.Concat);
                tokenI+=1;
                tokens[tokenI] = curToken;
            }else{
                tokens[tokenI] = curToken;
            }

            isInCharGroupingSquareBrack = (isInCharGroupingSquareBrack or (!isInCharGroupingSquareBrack and curToken.kind == Token.Kind.LSquareBrack)) and !(isInCharGroupingSquareBrack and curToken.kind == Token.Kind.RSquareBrack);
            tokenI+=1;
        }
        return try allocer.realloc(tokens, tokenI);
    }

    pub fn init(allocer:Allocator, input:[]const u8, diag:*Diag) !@This(){
        const tokens = try tokenize(allocer, input);
        return Tokenizer{
            .tokens = tokens,
            .cur = 0,
            .internalAllocator = allocer,
            .diag = diag,
        };
    }

    pub fn hasNext(self:*const Tokenizer) bool {
        return self.cur < self.tokens.len;
    }

    pub fn peekAssume(self:*const Tokenizer) Token {
        return self.tokens[self.cur];
    }

    pub fn peek(self:*const Tokenizer) SyntaxError!Token {
        if(!self.hasNext()){
            return SyntaxError.PrematureEnd;
        }

        return self.peekAssume();
    }

    pub fn nextAssume(self:*Tokenizer) Token {
        const tok = self.peekAssume();
        self.cur += 1;
        return tok;
    }

    pub fn next(self:*Tokenizer) SyntaxError!Token {
        if(!self.hasNext())
            return SyntaxError.PrematureEnd;

        return self.nextAssume();
    }

    pub fn nextOrNull(self:*Tokenizer) ?Token {
        if(!self.hasNext())
            return null;

        return self.nextAssume();
    }

    pub fn matchNext(self:*Tokenizer, kind:Token.Kind, comptime advance:bool) bool {
        if(self.hasNext() and self.peekAssume().kind == kind) {
            if (advance)
                self.cur += 1;
            return true;
        }
        return false;
    }

    pub fn assertNext(self:*Tokenizer, kind:Token.Kind) SyntaxError!void {
        if(!self.matchNext(kind, true)) {
            if(!self.hasNext()){
                return SyntaxError.PrematureEnd;
            }else{
                return SyntaxError.InvalidToken;
            }
        }
    }

    pub fn deinit(self:@This()) void {
        self.internalAllocator.free(self.tokens);
    }

    fn debugFmt(self:@This()) !std.ArrayList(u8) {
        var buf = try std.ArrayList(u8).initCapacity(cAllocer, self.tokens.len);
        const writer = buf.writer();
        for (self.tokens) |tok| {
            try writer.print("{?c}", .{tok.char});
        }
        return buf;
    }
};


const Parser = struct{
    allocer:Allocator,
    tok:*Tokenizer,
    diag:*Diag,

    pub fn init(allocer:Allocator, tok:*Tokenizer) @This() {
        return @This(){
            .allocer = allocer,
            .tok = tok,
            .diag = tok.diag,
        };
    }

    pub fn logError(self:*@This(), errorKind:ParseError) void {
        const msgStr:[:0]const u8 = switch(errorKind){
            error.OutOfMemory => "out of memory",
            error.RootExpressionInvalid => "root expression invalid, could not continue parsing",
            error.InvalidToken => "invalid token",
            error.PrematureEnd => "input ended prematurely",
            error.SemanticallyInvalidRange => "semantically invalid range in char group",
        };
        var location:Pair(u32, u32) = .{self.tok.cur, self.tok.cur+1};
        // try to get a better location depending on the error
        if(errorKind == error.SemanticallyInvalidRange){
            // can find the exact range to highlight: from the token before the last RangeMinus to the one after
            var rangeMinusIndex:u32 = self.tok.cur - 1;
            while(rangeMinusIndex > 0 and self.tok.tokens[rangeMinusIndex].kind != Token.Kind.RangeMinus){
                rangeMinusIndex -= 1;
            }
            location = .{rangeMinusIndex-|1, rangeMinusIndex+2};
        }
        self.diag.registerError(errorKind,  location, msgStr) 
            // if this is an error (has to be out of memory) we try to say 'help, something's going very wrong, we can't even register errors anymore'
            catch {
                std.io.getStdErr().writer().print("ran out of memory registering error: {} ({s})\n", .{errorKind, "a"}) catch {};
            };
    }

    pub fn parse(allocator:Allocator, regex:[]const u8) Tuple(&[_]type{ParseError!*RegEx, Diag}) {
        var diag = Diag.init(allocator);
        var tok = Tokenizer.init(allocator, regex, &diag) catch |err|{
            return .{err, diag};
        };
        var parser = Parser.init(allocator, &tok);
        defer tok.deinit();
        const res = parser.parseExpr(0);
        assert(isErr(res) or !tok.hasNext(), "tokenizer should be empty after successful parsing", .{});
        return .{res, diag};
    }

    pub fn parseNoDiagnostic(allocator:Allocator, regex:[]const u8) ParseError!*RegEx {
        const res, const diag =  Parser.parse(allocator, regex);
        diag.deinit();
        return res;
    }

    pub fn parsePrimaryExpr(self:*@This()) ParseError!*RegEx {
        const tok = self.tok;
        var primary:*RegEx = undefined;
        if(tok.matchNext(Token.Kind.LParen, true)) {
            primary = try self.parseExpr(0);
            try tok.assertNext(Token.Kind.RParen);
        }else if(tok.matchNext(Token.Kind.LSquareBrack, true)) {
            // char groups implemented as loop, that basically does [a-xyz] -> a-x|y|z
            // first of all: find all ranges
            var options = std.ArrayList(Pair(u8, u8)).init(self.allocer);
            defer options.deinit();

            const rangeStartIndex = tok.cur;

            const invert = tok.matchNext(Token.Kind.RangeInvert, true);

            while(!tok.matchNext(Token.Kind.RSquareBrack, true)) {
                // get current range
                const start = tok.nextAssume();
                if(start.kind != Token.Kind.Char) { //can't be anychar inside char group
                    return SyntaxError.InvalidToken;
                }

                var range:Pair(u8, u8) = .{start.char, start.char};

                if(tok.matchNext(Token.Kind.RangeMinus, true)){
                    const end = try tok.next();
                    if(end.kind != Token.Kind.Char) { //can't be anychar inside char group
                        return SyntaxError.InvalidToken;
                    }else if(end.char < range[0]) {
                        return ParseError.SemanticallyInvalidRange;
                    }

                    range[1] = end.char;
                }

                try options.append(range);
            }

            const rangeEndIndex = tok.cur;

            if(options.items.len > 1) {
                // sort the range options and try to unify the ranges (also eliminates duplicates)
                // TODO this could be done more efficiently using a custom sort that merges during the sorting, but this is fine for now, as we have such low n usually anyway

                // insertion sort because of low n
                std.sort.insertion(Pair(u8, u8), options.items, .{}, struct {fn f(_:@TypeOf(.{}), a:Pair(u8, u8), b:Pair(u8, u8)) bool { return a[0] < b[0]; }}.f);

                // merge (also inefficient rn)
                var i:i32 = 0;
                while(i < options.items.len - 1) : (i+=1) {
                    assert(i >= 0, "i should never be negative at the start of the loop (was: {})", .{i});
                    const uI:usize = @intCast(i);
                    if(options.items[uI][1] +| 1 >= options.items[uI+1][0]){
                        options.items[uI][1] = @max(options.items[uI][1], options.items[uI+1][1]);
                        // overall quadratic again, oof
                        _ = options.orderedRemove(uI+1);
                        // stay at the same index
                        i -= 1;

                        try self.diag.warn(.{rangeStartIndex, rangeEndIndex}, "overlapping or adjacent ranges in char group (merged automatically)");
                    }
                }
            }


            if(invert){
                // edge case: in the very unlikely case (from a user perspective) that the first range starts at 1, we need to simply remove it. This is O(n), but so unlikely (and n usually so small), that it shouldn't matter much

                var lastRangeEnd:u8 = 0;

                if(options.items.len > 0 and options.items[0][0] == 1){
                    lastRangeEnd = options.orderedRemove(0)[1];
                }

                for(options.items) |*range| {
                    assert(range[0] != 0, "invalid range start", .{});
                    const oldRange = range.*;
                    range[0] = lastRangeEnd + 1;
                    range[1] = oldRange[0] - 1;
                    lastRangeEnd = oldRange[1];
                }
                // append last range (edge case: except when the last range ends at 255, then the range to append would be empty, so omit it)
                if(lastRangeEnd < 255){
                    try options.append(.{lastRangeEnd + 1, 255});
                }
            }
            

            // now we have all ranges, we need to convert them to a regex
            // we do this by successively creating full subtrees (every inner node is a union), and then union-ing them together again, basically bottom-up
            // we create these by descending size

            var currentRoot = try self.allocer.create(RegEx);
            currentRoot.* = RegEx.initLiteralChar(self.allocer, RegExNFA.epsilon); // if the options are empty, we need an empty char, if not, this will get overwritten
            var currentSubtree = currentRoot;
            while(options.items.len>0){
                const subtreeHeight = std.math.log2_int(usize, options.items.len) + 1; // the log is basically the depth, but we want a height, so we add 1
                if(subtreeHeight > 32) 
                    return error.OutOfMemory;

                const numInnerNodes = (oldIntCast(1, usize) << (subtreeHeight - 1)) - 1;
                const numTotalNodes = (oldIntCast(1, usize) << subtreeHeight) - 1;
                var worklist = try std.ArrayList(*RegEx).initCapacity(self.allocer, numTotalNodes);
                defer worklist.deinit();
                worklist.appendAssumeCapacity(currentSubtree);
                var handled:usize = 0;
                // this loop initializes the inner nodes
                while(handled < numInnerNodes) : (handled+=1) {
                    const left = try self.allocer.create(RegEx);
                    const right = try self.allocer.create(RegEx);

                    worklist.items[handled].* = RegEx.initOperator(self.allocer, Token.Kind.Union, left, right);

                    worklist.appendAssumeCapacity(left);
                    worklist.appendAssumeCapacity(right);
                }

                // we've handled all inner nodes, everything that's remaining are the leaves
                for(worklist.items[handled..]) |leaf| {
                    // don't need to check whether there are options left, the construction of the subtree guarantees that there are
                    // TODO could not do pop and keep track of an index ourselves (then the order would also not be reversed), but this is fine, and a bit more readable
                    leaf.* = RegEx.initLiteralChars(self.allocer, options.pop());
                }

                // -> we've constructed a full subtree
                // if there are more ranges left, we need to union the current subtree with the next one
                if(options.items.len > 0){
                    const newRoot = try self.allocer.create(RegEx);
                    currentSubtree = try self.allocer.create(RegEx);
                    newRoot.* = RegEx.initOperator(self.allocer, Token.Kind.Union, currentRoot, currentSubtree);
                    currentRoot = newRoot;

                    // -> the next iteration will fill the newRoots right subtree as the currentSubtree
                }
            }

            primary = currentRoot;
        }else if(!tok.hasNext()) {
            return SyntaxError.PrematureEnd;
        }else{
            primary = try self.allocer.create(RegEx);
            errdefer self.allocer.destroy(primary);

            if(tok.matchNext(Token.Kind.AnyChar, true)) {
                // anychar is just a range from 1 to 255 (0 is an invalid char in the final string (as it denotes the end of the string), later we use it to represent an epsilon transition)
                primary.* = RegEx.initLiteralChars(self.allocer, .{1, 255});
            }else{
                if(tok.peekAssume().kind != Token.Kind.Char) {
                    return SyntaxError.InvalidToken;
                }
                primary.* = RegEx.initLiteralChar(self.allocer, tok.nextAssume().char);
            }
        }

        // unary operators
        // precedence is ignored because its the highest anyway
        if(tok.matchNext(Token.Kind.Kleen, true)) {
            const kleen = try self.allocer.create(RegEx);
            kleen.* = RegEx.initOperator(self.allocer, Token.Kind.Kleen, primary, null);
            return kleen;
        }else if(tok.matchNext(Token.Kind.Plus, true)) {
            const kleen = try self.allocer.create(RegEx);
            kleen.* = RegEx.initOperator(self.allocer, Token.Kind.Kleen, primary, null);

            const first = try primary.deepClone();
            
            const concat = try self.allocer.create(RegEx);
            concat.* = RegEx.initOperator(self.allocer, Token.Kind.Concat, first, kleen);
            return concat;
        }else if(tok.matchNext(Token.Kind.Question, true)) {
            const eps = try self.allocer.create(RegEx);
            eps.* = RegEx.initLiteralChar(self.allocer, RegExNFA.epsilon);

            const yunyin = try self.allocer.create(RegEx);
            yunyin.* = RegEx.initOperator(self.allocer, Token.Kind.Union, primary, eps);

            return yunyin;
        }else{
            return primary;
        }
    }

    // TODO currently, a parsing error results in memory not being freed. In the main use case, this uses an arena anyway, so it shouldn't be a big problem, but it's still not nice

    // TODO think about what error to return in case there are multipl errors, and how to best recover from an error to continue parsing at a higher level in the tree
    pub fn parseExpr(self:*@This(), minPrec:u32) ParseError!*RegEx {
        const tok = self.tok;

        var lhs:?*RegEx = self.parsePrimaryExpr() catch |err| lhs: {
            self.logError(err);
            break :lhs null;
        };
        // TODO test this - this should always only deinit everything once, but I'm also not sure what happens if lhs gets overridden in the loop - does errdefer capture it? etc.
        errdefer if (lhs) |lhs0| lhs0.deinit();
        while (tok.hasNext()) {
            // let the upper level parse 'unknown operators' (in this case anything but the binary operators)
            const operatorKind = tok.peekAssume().kind; // we peek, because if we return inside the loop, the upper level needs to consume that token
            if(operatorKind != Token.Kind.Union and operatorKind != Token.Kind.Concat)
                return lhs orelse ParseError.RootExpressionInvalid;

            const prec = operatorKind.precedenceAndChar().prec;
            if (prec < minPrec)
                return lhs orelse ParseError.RootExpressionInvalid;

            _ = tok.nextAssume(); // consume operator


            // new precedence always + 1, because we only have left-associative operators, so we want to bind the same operator again in the next depth, not in the one above
            const rhs = try self.parseExpr(prec + 1);
            const op = self.allocer.create(RegEx) catch {
                self.logError(error.OutOfMemory);
                lhs.?.deinit();
                rhs.deinit();
                return error.OutOfMemory;
            };
            op.* = RegEx.initOperator(self.allocer, operatorKind, lhs, rhs);
            lhs = op;
        }
        return lhs orelse ParseError.RootExpressionInvalid;
    }
};

const RegEx = struct {
    kind:Token.Kind,
    left:?*RegEx,
    right:?*RegEx,
    chars:Pair(u8,u8),

    internalAllocator:Allocator,

    // for DFA conversion
    nfaStartState:?u32,
    nfaEndState:?u32,

    pub fn initLiteralChar(allocer:Allocator, char:u8) @This() {
        return RegEx{
            .left = null,
            .right = null,
            .kind = Token.Kind.Char,
            .chars = .{char, char},
            .internalAllocator = allocer,
            .nfaStartState = null,
            .nfaEndState = null,
        };
    }

    pub fn initLiteralChars(allocer:Allocator, chars:Pair(u8, u8)) @This() {
        return RegEx{
            .left = null,
            .right = null,
            .kind = Token.Kind.Char,
            .chars = chars,
            .internalAllocator = allocer,
            .nfaStartState = null,
            .nfaEndState = null,
        };
    }

    pub fn initOperator(allocer:Allocator, kind:Token.Kind, left:?*RegEx, right:?*RegEx) @This() {
        return RegEx{
            .left = left,
            .right = right,
            .kind = kind,
            .chars = .{0,0},
            .internalAllocator = allocer,
            .nfaStartState = null,
            .nfaEndState = null,
        };
    }

    // uses the internal allocator to perform a deep clone
    pub fn deepClone(self:*@This()) !*@This() {
        var clone = try self.internalAllocator.create(RegEx);
        clone.kind = self.kind;
        clone.chars = self.chars;

        clone.left = 
            if(self.left) |left|
                try left.*.deepClone()
            else
                null;

        clone.right = 
            if(self.right) |right|
                try right.*.deepClone()
            else
                null;

        clone.internalAllocator = self.internalAllocator;

        clone.nfaStartState = self.nfaStartState;
        clone.nfaEndState = self.nfaEndState;

        return clone;
    }

    pub fn deinit(self:*@This()) void {
        if(self.left) |left| {
            left.deinit();
        }
        if(self.right) |right| {
            right.deinit();
        }
        self.internalAllocator.destroy(self);
    }


    pub fn isOperator(self:RegEx) bool {
        // if left is null (i.e. this is a leaf), right must be null too
        assert(self.left != null or self.right == null, "regex has no left operand, but right operand is not null", .{});
        return self.left != null;
    }

    fn printDOTInternal(self:RegEx, writer:anytype, num:u128) !void {
        // depth above 127 is undefined for now
        try writer.print("n{}[label=\"{}\"];", .{num, self});

        if (self.left) |left| {
            try writer.print("n{} -> n{};",   .{num, num << 1});
            try left.printDOTInternal(writer, num << 1);
        }
        if (self.right) |right| {
            try writer.print("n{} -> n{};",    .{num, (num << 1) + 1});
            try right.printDOTInternal(writer, (num << 1) + 1);
        }
    }

    pub fn printDOTRoot(self:RegEx, writer:anytype) !void {
        try writer.print("digraph RegEx {{", .{});
        try self.printDOTInternal(writer, 1);
        try writer.print("}}\n", .{});
    }

    // if called without options, this function just uses the RegEx's allocator for the DFA, i.e. that allocators lifetime has to exceed the lifetime of the DFA
    pub fn toDFA(self:*@This(), opts:struct{overrideAllocator:?Allocator = null}) !RegExDFA {
        // broad overview: convert regex to eps-nfa to nfa to dfa.
        // vague idea (mostly my own, no idea if this is good): 
        // 1. iterate in post order over the AST, create and save start and end states for each operator node (all except the leafs), and connect the with the transitions. Distinguish between whether the operator has leaf- (i.e. char-) operands or other operator operands
        //    -> this implies the construction will not be that efficient, as we sometimes need to create new states + transitions to be able to save only one start/end state (for example for |)
        // 2. designate full start/end states for the whole regex
        // 3. back up eps transitions
        // 4. convert to dfa

        // edge case: no operators, i.e. just a single char (could also be epsilon)
        // we need to handle this separately, because the main tree traversal only traverses inner nodes (operators), and analyzes the children of those, so we would miss this singular leaf
        if(!self.isOperator()) {
            var dfa = try RegExDFA.init(self.internalAllocator);
            dfa.startState = 
                try dfa.addState();

            if(self.chars[0] == RegExNFA.epsilon) {
                // if the transition includes an epsilon, we need to add 0 as a final state, and ...
                try dfa.designateStatesFinal(&[1]u32{0});
                // if the transition is not empty, we need to add a state, and a transition from 0 to 1
                if(self.chars[1] != RegExNFA.epsilon){
                    try dfa.addStates(1);
                    try dfa.designateStatesFinal(&[1]u32{1});
                    // the transition starts from the char after epsilon
                    try dfa.transitions[dfa.startState].insert(RegExNFA.epsilon + 1, self.chars[1], 1, .{});
                } // otherwise, we just have the dfa that only accepts the empty string
            } else {
                try dfa.addStates(1);
                // if there's no epsilon, just build a simple (0) -[chars]-> ((1)) dfa, i.e. with 1 as a final state
                try dfa.designateStatesFinal(&[1]u32{1});
                try dfa.transitions[dfa.startState].insert(self.chars[0], self.chars[1], 1, .{});
            }


            return dfa;
        }

        var arena = std.heap.ArenaAllocator.init(cAllocer);
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

                    // TODO this can be optimized (for compile-time), we don't need a new start/end state in every case. But it does not save huge amounts of time, we will just have a bunch of unused states in the nfa, that won't be added to the dfa, because they're never reached from the start state
                    try nfa.addStates(2);
                    cur.regex.nfaStartState = nfa.numStates - 2;
                    const curStartState = cur.regex.nfaStartState.?;
                    cur.regex.nfaEndState = nfa.numStates - 1;
                    const curEndState = cur.regex.nfaEndState.?;

                    const epsilon = RegExNFA.epsilon;

                    // in the operator, connect the start/end states of the operands with the operator
                    switch(cur.regex.kind){
                        Token.Kind.Union => {
                            const right = cur.regex.right.?;

                            if(!left.isOperator()){
                                try nfa.addRangeTransitionByState(curStartState, left.chars, &[_]u32{curEndState});
                            }else{
                                // if it is an operator, we have visited it before, so it has a start/end state, so we can just connect it
                                try nfa.addSingleTransition(left.nfaEndState.?, epsilon, curEndState);

                                // also connect the start state of the operator with the start state of the left operand
                                try nfa.addSingleTransition(curStartState, epsilon, left.nfaStartState.?);
                            }

                            if(!right.isOperator()){
                                try nfa.addRangeTransitionByState(curStartState, right.chars, &[_]u32{curEndState});
                            }else{
                                // same as left
                                try nfa.addSingleTransition(right.nfaEndState.?, epsilon, curEndState);
                                try nfa.addSingleTransition(curStartState, epsilon, right.nfaStartState.?);
                            }
                            // sidenote: see? this is exactly why every programming language needs the ability to use 'local functions'/lambdas for readability. Do you hear me, Zig? :. Don't even need to be real functions in the end, can just inline all of them (and forbid non-inlinable ones)
                        },
                        Token.Kind.Concat => {
                            const right = cur.regex.right.?;

                            if(left.isOperator() and right.isOperator()){
                                // if both are operators, we have visited them before, so they have start/end states, so we can just connect them
                                try nfa.addSingleTransition(left.nfaEndState.?, epsilon, right.nfaStartState.?);
                                // and set the start/end of this operator to the start/end of the operands
                                cur.regex.nfaStartState = left.nfaStartState.?;
                                cur.regex.nfaEndState = right.nfaEndState.?;
                            }else if(left.isOperator()){
                                // if only left is an operator, we can take the existing end state of left and connect it with the char of right to the new end state
                                try nfa.addRangeTransitionByState(left.nfaEndState.?, right.chars, &[_]u32{curEndState});
                                cur.regex.nfaStartState = left.nfaStartState.?;
                            }else if(right.isOperator()){
                                // same as left
                                try nfa.addRangeTransitionByState(curStartState, left.chars, &[_]u32{right.nfaStartState.?});
                                cur.regex.nfaEndState = right.nfaEndState.?;
                            }else{
                                // if both are chars, we need one more state in between
                                const inBetweeny = try nfa.addState();
                                try nfa.addRangeTransitionByState(curStartState, left.chars,  &[_]u32{inBetweeny});
                                try nfa.addRangeTransitionByState(inBetweeny,    right.chars, &[_]u32{curEndState});
                            }

                        },
                        Token.Kind.Kleen => {
                            if(left.isOperator()){
                                // we just reuse all of the operator and connect the end state with the start state
                                try nfa.addSingleTransition(left.nfaEndState.?, epsilon, left.nfaStartState.?);
                                cur.regex.nfaStartState = left.nfaStartState.?;
                                cur.regex.nfaEndState = left.nfaEndState.?;

                                // also connect the start state with the end state, to be able to match the empty string by skipping the sequence of states entirley
                                try nfa.addSingleTransition(left.nfaStartState.?, epsilon, left.nfaEndState.?);
                            }else{
                                // just use the start state as start/end
                                // and add a transition to itself
                                try nfa.addRangeTransitionByState(curStartState, left.chars, &[_]u32{curStartState});
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

        return try nfa.toPowersetConstructedDFA(.{.overrideAllocator = opts.overrideAllocator orelse self.internalAllocator});
    }

    pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        if(self.isOperator()){
            try writer.print("{c}", .{self.kind.precedenceAndChar().char});
        }else{
            try formatTransitionChars(self.chars, writer);
        }
    }

    // mostly for debugging/testing
    pub fn traverse(self: *@This(), comptime visitor: fn(*RegEx, // node
            bool, // isLeaf
            usize, // depth
        ) anyerror!void) !void {
        try self.traverseInner(visitor, 0);
    }

    fn traverseInner(self: *@This(), comptime visitor: fn(*RegEx, bool, usize) anyerror!void, depth:usize) !void {
        const hasLeft = self.left != null; 
        const hasRight = self.right != null;

        try visitor(self, !hasLeft and !hasRight, depth);
        if(hasLeft) {
            try self.left.?.traverseInner(visitor, depth + 1); 
        }
        
        if(hasRight) {
            try self.right.?.traverseInner(visitor, depth + 1);
        }
    }
};

// (eps-)NFA, removing eps transitions, powerset construction, then we can simply construct the eps-NFA from the regex and then convert it to a DFA to perform checks

// alphabet is implicitly the space of u8.
// passing an arena allocator and *not* calling deinit on the DFA, just on the arena is recommended. If you need to use another allocator, call deinit on the DFA directly
const RegExDFA = struct{
    const EntireTransitionMapOfAState = RangeMap(u8, makeOrder(u8), u32);
    const UniqueStateSet              = ArraySet(u32, makeOrder(u32));

    const defaultTransitionCapacityForState = 2;

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
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

    pub fn isInLanguageInterpreted(self:@This(), word:[]const u8) bool{
        var curState:u32 = self.startState;
        for(word) |c| {
            curState = self.transitions[curState].find(c) orelse return false;
        }
        return self.finalStates.contains(curState);
    }

    const ProfilingInformation = struct{
        transitionFequencyPerState:[]EntireTransitionMapOfAState, // instead of mapping to a state, we map to a frequency (also a u32)
        // only counts if we left the state again (so that all transition frequencies add up to the number of visits)
        // TODO this is not used yet, but might of course be useful at some point
        visitsPerState:[]u32,

        internalAllocator:Allocator,

        pub fn init(allocer:Allocator, numStates:u32) !@This() {
            const info = ProfilingInformation{
                .transitionFequencyPerState = try allocer.alloc(EntireTransitionMapOfAState, numStates),
                .visitsPerState = try allocer.alloc(u32, numStates),
                .internalAllocator = allocer,
            };

            @memset(info.visitsPerState, 0);

            for (info.transitionFequencyPerState) |*transitions| {
                transitions.* = try EntireTransitionMapOfAState.init(allocer);
            }

            return info;
        }

        pub fn deinit(self:@This()) void {
            for (self.transitionFequencyPerState) |transitions| {
                transitions.deinit();
            }
            self.internalAllocator.free(self.transitionFequencyPerState);
            self.internalAllocator.free(self.visitsPerState);
        }
    };

    pub fn staticallyProfileOneRun(self:@This(), word:[]const u8, profile:*ProfilingInformation) !void {
        var curState:u32 = self.startState;
        for(word) |c| {
            // possibly return first so that the visit count only counts if we left the state again
            const nextState = self.transitions[curState].find(c) orelse return;

            profile.visitsPerState[curState] += 1;
            var spot = try profile.transitionFequencyPerState[curState].findOrMakeSpot(c, .{});
            if(spot.found_existing){
                spot.value().* += 1;
            }else{
                spot.setRange(c, c);
                spot.value().* = 1;
            }

            curState = nextState;
        }
    }

    const CompilationError = error{DFATooLargeError, NotYetImplemented} || FeError || std.posix.MMapError;

    const CompiledRegExDFA = struct{
        jitBuf:[]u8,
        finalStates:*const UniqueStateSet,
        recognize:*fn(*const UniqueStateSet, word:[:0] const u8) bool,

        pub fn isInLanguageCompiled(self:@This(), word:[:0] const u8) bool{
            return self.recognize(self.finalStates, word);
        }

        // finalStates obviously needs to have a lifetime that is at least as long as the compiled DFA
        pub fn init(finalStates:*const UniqueStateSet) std.posix.MMapError!@This() {
            // we just map 2 GiB by default, and mremap it later to the actual size
            return CompiledRegExDFA{
                .jitBuf = try std.posix.mmap(
                    null,
                    1 << 31,
                    std.posix.PROT.READ | std.posix.PROT.WRITE | std.posix.PROT.EXEC,
                    .{.TYPE = .PRIVATE, .ANONYMOUS = true},
                    -1,
                    0,
                ),
                .finalStates = finalStates,
                .recognize = undefined,
            };
        } 

        pub fn shrinkToSize(self:*@This(), shrunkSize:usize) !void {
            self.jitBuf.len = shrunkSize;
            // call mremap through direct syscall, no zig bindings yet :(
            // (page align length first)
            const alignedLen = std.mem.alignForward(usize, self.jitBuf.len, std.mem.page_size); // TODO this is just a 'minimum page size'

            const ret = std.os.linux.syscall4(.mremap, @intFromPtr(self.jitBuf.ptr), 1 << 31, alignedLen, 0);
            if(ret < 0)
                return error.MMapError;

            assert(ret == @intFromPtr(self.jitBuf.ptr), "mremap returned a different pointer than the one we passed, even though we should only be shrinking", .{});
            //self.jitBuf.ptr = @ptrFromInt(ret);
        }

        pub fn deinit(self:@This()) void {
            std.os.munmap(self.jitBuf.ptr, self.jitBuf.len);
        }

        pub fn debugPrint(self:@This()) void {
            debugLog("compiled DFA:", .{});

            var cur = self.jitBuf.ptr;
            while(@intFromPtr(cur) < @intFromPtr(self.jitBuf.ptr) + self.jitBuf.len) {
                if(@intFromPtr(cur) == @intFromPtr(self.recognize))
                    debugLog("start of regognize:", .{});

                var instr:fadec.FdInstr = undefined;

                const numBytes = fadec.fd_decode(cur, self.jitBuf.len, 64, 0, &instr);
                if(numBytes < 0){
                    debugLog("error decoding instruction at byte: {}", .{numBytes});
                    return;
                }
                cur += oldIntCast(numBytes, usize);

                var fmtBuf:[64:0]u8 = undefined;
                fadec.fd_format(&instr, &fmtBuf, fmtBuf.len);

                debugLog("{s}", .{@as([*:0]u8, &fmtBuf)});
            }
        }
    };

    // TODO could the compilation somehow be SIMD-d? doing all the comparisons at once might be faster, but the branching and scalar/vector mixing might make it slower than normal

    // for now, requires that the self-DFA has been allocated with an arena (and this arena has been passed), to be able to ensure the total code size will be < 2 GiB
    // for now, requires the original DFA to be live for the lifetime of the compiled DFA, because it needs to be able to access the final states
    // TODO there has to be a better way to do this comptime bool thing. A nullable profile info wouldn't generate a different function per bool value, i.e. cost runtime performance (I think)
    pub fn compile(self:@This(), arena:*std.heap.ArenaAllocator, comptime hasProfileInfo:bool, opts:struct{profileInfo:ProfilingInformation = undefined, comptime stopOnFinalState:bool = true}) CompilationError!CompiledRegExDFA{
        // there are different options for implementing the jumps to the next state, equivalent to the approaches for lowering switch statements:
        // let's try a linear if-else chain first (could later order this by estimated frequency of each transition, by profiling this on the interpreted version). Should be fastest for a low number of transitions per state 
        // - binary search based switching might be fastest, if the number of transitions per state is medium to high
        // - indirect jumps using hashtables might be fastest, if branch target buffer overflows aren't too common, or if the number of transitions per state is very high

        // there are 2 options for checking whether we have the final char:
        // - either check when/after increasing the pointer, if we are at the end of the word
        //   - this would incur a check for every char, but would not make the function harder to use
        // - or make sure the word is zero terminated, and include a branch to a check on the current char being zero
        //   - this would only incur a check if we actually reached the end of the word, but require the user to have a zero-terminated string, and it forbids using fallthrough for the last possible transition (although - with profiling info - that should be the most unlikely one)
        //   - currently only this option is implemented

        // TODO re-do this calculation considering the new ranges feature
        const executableRegionSizeEstimate = 
            // data region
            // nothing for if-else chain or binary search based solutions
            0
            +
            // text/code region
            // for each state:
            // add rax, 1 (4 bytes); increment the pointer to the word (inc rax would be 3 bytes, but Agner Fog recommends not to use inc, so add it is for now)
            // mov cl, BYTE PTR [rax] (2 bytes); load the current char into cl for comparisons
            // <transitions, see below>
            // end:
            // - fallthrough for last transition and jne <trap state>
            // - or normal je for last transition, and then a jmp <trap state> 
            self.numStates*(4+2)
            +
            // lets say approx. 3 transitions per state
            // per transitions for the if-else chain:
            // cmp cl, IMM (3 bytes)
            // je (6 bytes (short encoding (3 bytes) is likely for some, but not all)) for each transition
            self.numStates*3*(3+6)
            // each indirect branch of the form `jmp [rax-0xbeef]` is 6 bytes long
            // -> for the indirect branch model this is an exact estimate
            //self.numStates*6
            ;
        _ = executableRegionSizeEstimate;

        // this is obviously a ridiculous overestimate, but it is definitely safe, and should still allow gargantuan regexes
        const upperMemoryLimit = arena.queryCapacity() * (3+6) + self.numStates*(4+2);
        if(upperMemoryLimit > 1 << 31)
            return error.DFATooLargeError;


        var compiledDFA = try CompiledRegExDFA.init(&self.finalStates);

        const buf = compiledDFA.jitBuf;
        var cur:[*]u8 = buf.ptr;

        // setup
        // register layout (at the start, rsi contains the pointer to the word, but that is overridden immediately):
        // rax: pointer to word
        // cl: constantly updated to contain the current char of the word
        // rdi: pointer to finalStates for checking whether the state at the end is a final state
        // rsi: current state

        // generate trap state code at the start -> we know the jump offset right away
        // trap state -> return false
        const trapStatePtr = cur; 

        try encode(&cur, fadec.FE_ADD64ri, .{fadec.FE_SP, 8});
        try encode(&cur, fadec.FE_MOV64ri, .{fadec.FE_AX, @intFromBool(false)});
        try encode(&cur, fadec.FE_RET, .{});

        // same idea for the code for reaching the end of the word
        const checkFinalStatePtr = cur;
        
        // we basically need to do:
        // return finalStates.contains(curState);
        // so just call that function, and pass on its return value to the caller of our function
        // we can do this even quicker by not even using a call, but just cleaning up our whole stackframe and jumping there immediately. Our return address will then be used by finalStates.contains to return to the proper place. Also keeps the CPU shadow call stack in tact.

        // stack cleanup and "return" (by jumping to finalStates.contains)
        try encode(&cur, fadec.FE_ADD64ri, .{fadec.FE_SP, 8});
        // finalStates self arg is already in RDI, stays there from the call to this function
        // real arg (the state to check) is implicitly already in RSI, the states that branch to this code segment put their own state number in RSI

        // mov rax, finalStates.contains
        try encode(&cur, fadec.FE_MOV64ri, .{fadec.FE_AX, oldIntCast(@intFromPtr(&UniqueStateSet.contains), fadec.FeOp)});
        // jmp rax
        try encode(&cur, fadec.FE_JMPr, .{fadec.FE_AX});

        const recognizerFunctionEntryPtr = cur;

        // stackframe setup
        // align stack to 16 bytes
        try encode(&cur, fadec.FE_SUB64ri, .{fadec.FE_SP, 8});

        // mov rax, rsi; move the passed pointer to the word into rax
        try encode(&cur, fadec.FE_MOV64rr, .{fadec.FE_AX, fadec.FE_SI});


        // traverse the DFA in BFS from the start state (to try to ensure that jumps are as short as possible and some can be left out if they're the last option)
        var worklist = try std.ArrayList(u32).initCapacity(self.internalAllocator, self.numStates);
        defer worklist.deinit();
        worklist.appendAssumeCapacity(self.startState);
        // we're not removing from the worklist, moving elements to do that would be unnecessary

        var scheduledForVisit = try self.internalAllocator.alloc(bool, self.numStates);
        defer self.internalAllocator.free(scheduledForVisit);
        @memset(scheduledForVisit, false);
        scheduledForVisit[self.startState] = true;

        var startOfState = try self.internalAllocator.alloc(?*u8, self.numStates);
        defer self.internalAllocator.free(startOfState);
        @memset(startOfState, null);

        var jumpsToPatch = try std.ArrayList(struct{instrToPatch:*u8, opcode:FeMnem, targetState:u32}).initCapacity(self.internalAllocator, self.numStates);
        defer jumpsToPatch.deinit();

        var worklistI:usize = 0;
        while(worklistI < self.numStates) : (worklistI += 1) {
            // TODO if there are any unreachable states, this will panic. unreachable states are impossible if generated from powerset construction, but still, this should be handled more gracefully
            const curState = worklist.items[worklistI];
            startOfState[curState] = @ptrCast(cur);

            // get current char
            try encode(&cur, fadec.FE_MOV8rm, .{fadec.FE_CX, std.math.minInt(i64) | oldIntCast(fadec.FE_AX, i64) << 32}); // std.math.minInt(i64) | ... << 32 is the same as FE_MEM(FE_AX, 0, 0, 0), but that doesn't work, c translation does not work there

            // increment the pointer
            try encode(&cur, fadec.FE_ADD64ri, .{fadec.FE_AX, 1});


            var curTransitionsOrdered:EntireTransitionMapOfAState = undefined;
            defer if(hasProfileInfo) curTransitionsOrdered.deinit();

            // if there is any - use the profiling info to sort the transitions
            if(hasProfileInfo) {
                // TODO this functionality is probably quite slow overall in terms of compile-time, because of the cloning, sorting, etc.
                curTransitionsOrdered = try self.transitions[curState].clone();

                const transitionFequency = opts.profileInfo.transitionFequencyPerState[curState];
                const RangedTransition = Pair(u8, Pair(u8, u32));
                const lambda = struct{
                    fn f(transitionFequencyLocal:@TypeOf(transitionFequency), a:RangedTransition, b:RangedTransition) bool {
                        return transitionFequencyLocal.find(a[0]) orelse 0 > transitionFequencyLocal.find(b[0]) orelse 0;
                    }
                }.f;
                std.sort.pdq(RangedTransition, curTransitionsOrdered.map.items, transitionFequency, lambda);

                assert(curTransitionsOrdered.map.items.len == 0 or transitionFequency.find(curTransitionsOrdered.map.items[0][0]) orelse 0 >= transitionFequency.find(curTransitionsOrdered.map.items[curTransitionsOrdered.map.items.len-1][0]) orelse 0, "sorting didnt work", .{});
            }else{
                // copy shouldnt be a problem, is only copying fat pointers, right?
                curTransitionsOrdered = self.transitions[curState];
            }

            // I hate that zig has no proper way to do this...
            // literally makes the language unusable for me
            // and no, the userspace solutions are not sufficiently easy
            const encodeMinimizedJump = struct{
                fn f(curPtr:*[*]u8, jumpsToPatch0:anytype, startOfState0:anytype, targetState:u32, jmpKind:FeMnem) !void{
                    if(startOfState0[targetState]) |jeTarget| {
                        // just encode, and let fadec pick the best encoding
                        try encode(curPtr, jmpKind, .{oldIntCast(@intFromPtr(jeTarget), fadec.FeOp)});
                    }else{
                        try jumpsToPatch0.*.append(.{.instrToPatch = @ptrCast(curPtr.*), .opcode = jmpKind, .targetState = targetState});
                        // use longest possible encoding to reserve space, patch it later
                        try encode(curPtr, jmpKind | fadec.FE_JMPL, .{oldIntCast(@intFromPtr(curPtr.*), fadec.FeOp)});
                    }
                }
            }.f;

            // normally:
            // traverse all possible transitions and emit instructions that check for them, and jump to the respective target state
            // if it's the end of the word, jump to the final state check function
            // if it's not the end of the word and we haven't found a transition, jump to the trap state
            // (this is done by the for loop below)
            // but for anychar, this is easier:

            // additional check for '.'/AnyChar, i.e. if the range is 1-255, just check that it's not 0, if it's not, jump to the target. If it is 0, skip the normal insertion of another cmp cl, 0, and do the JZ immediately
            if(curTransitionsOrdered.map.items.len == 1){ 
                const targetState = curTransitionsOrdered.map.items[0][1][1];
                const startChar = curTransitionsOrdered.map.items[0][1][0];
                const endChar = curTransitionsOrdered.map.items[0][0];

                if(startChar == 1 and endChar == 255){
                    // add to the worklist
                    if(!scheduledForVisit[targetState]) {
                        worklist.appendAssumeCapacity(targetState);
                        scheduledForVisit[targetState] = true;
                    }

                    try encode(&cur, fadec.FE_CMP8ri, .{fadec.FE_CX, 0});
                    // if not zero: jump to target state 
                    // je targetState
                    try encodeMinimizedJump(&cur, &jumpsToPatch, startOfState, targetState, fadec.FE_JNZ);
                    // otherwise it's zero, i.e. the end of the word (basically the same code as after the for loop, just without the trap state, and with an unconditional jump. Again @Zig, this is why you need local lambdas)
                    // if we have, jump to the checkFinalStatePtr and move the current state into RSI
                    // TODO instruction scheduling-wise: might make sense to put the mov at the start (for better out of order execution), although it would cost a bit of decoding performance even if its not executed, which is not the case here. Test this
                    try encode(&cur, fadec.FE_MOV64ri, .{fadec.FE_SI, curState});
                    try encode(&cur, fadec.FE_JMP, .{oldIntCast(@intFromPtr(checkFinalStatePtr), fadec.FeOp)});

                    continue;
                }
            }

            for(curTransitionsOrdered.map.items) |transition| {
                const range:Pair(u8,u8) = .{transition[1][0], transition[0]};
                const targetState = transition[1][1];

                // add to the worklist
                if(!scheduledForVisit[targetState]) {
                    worklist.appendAssumeCapacity(targetState);
                    scheduledForVisit[targetState] = true;
                }

                // do the actual work

                // single char transition
                if(range[0] == range[1]){
                    // because fadec expects signed operands (i64), we need to use signed chars as well, i.e. i8. If we don't, then zig will implicitly widen the u8 to an i64, meaning e.g. 255 would become 0x00...00ff, not 0xff...ff like we want it to, i.e. it wouldn't get sign-extended. We need the sign extension for stuff to still be encoded correctly. Arguably a minor fault in fadec's operand types
                    const char:i8  = @bitCast(range[0]);

                    // cmp cl, transitionChar
                    try encode(&cur, fadec.FE_CMP8ri, .{fadec.FE_CX, char});

                    // je targetState
                    try encodeMinimizedJump(&cur, &jumpsToPatch, startOfState, targetState, fadec.FE_JZ);
                }else{
                    const startChar:i8 = @bitCast(range[0]);
                    const endChar:i8  = @bitCast(range[1]);

                    // cmp cl, startChar
                    try encode(&cur, fadec.FE_CMP8ri, .{fadec.FE_CX, startChar});

                    // if cl < startChar, jump to next transition (jump needs to be patched later)
                    // don't need to use FE_JMPL, because we know the target is <128 away
                    const FE_JB = fadec.FE_JC; // jump below == jump carry
                    var toPatch = cur;
                    try encode(&cur, FE_JB, .{oldIntCast(@intFromPtr(cur), fadec.FeOp)}); // TODO could also hard code this instead of patching it, if we always use a long jump for the JBE later, performance test whether that's worth it

                    // cmp cl, endChar
                    try encode(&cur, fadec.FE_CMP8ri, .{fadec.FE_CX, endChar});

                    // if cl <= endChar, jump to target like above
                    try encodeMinimizedJump(&cur, &jumpsToPatch, startOfState, targetState, fadec.FE_JBE);

                    // patch jump from before to jump to here
                    const nextTransitionPatchTarget = cur;
                    try encode(&toPatch, FE_JB, .{oldIntCast(@intFromPtr(nextTransitionPatchTarget), fadec.FeOp)});
                }
            }

            // check if we have reached the end of the word
            try encode(&cur, fadec.FE_CMP8ri, .{fadec.FE_CX, 0});
            // if we have, jump to the checkFinalStatePtr and move the current state into RSI
            // TODO instruction scheduling-wise: might make sense to put the mov at the start (for better out of order execution), although it would cost a bit of decoding performance even if its not executed, which is not the case here. Test this
            try encode(&cur, fadec.FE_MOV64ri, .{fadec.FE_SI, curState});
            try encode(&cur, fadec.FE_JZ, .{oldIntCast(@intFromPtr(checkFinalStatePtr), fadec.FeOp)});

            // trap state
            try encode(&cur, fadec.FE_JMP, .{oldIntCast(@intFromPtr(trapStatePtr), fadec.FeOp)});
        }

        // patch jumps
        for(jumpsToPatch.items) |*jump| {
            try encode(@ptrCast(&jump.instrToPatch), jump.opcode | fadec.FE_JMPL, .{oldIntCast(@intFromPtr(startOfState[jump.targetState].?), fadec.FeOp)});
        }

        compiledDFA.recognize = @ptrCast(recognizerFunctionEntryPtr);

        try compiledDFA.shrinkToSize(@intFromPtr(cur)-@intFromPtr(buf.ptr));

        return compiledDFA;
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
        try writer.print("{{ node[shape=circle]; mode = \"hier\"; layout = \"neato\"; overlap=\"scale\"; sep=\"+40\"", .{});

        const startState = switch(self){
            inline else => |case| case.startState
        };

        const finalStates = switch(self){
            inline else => |case| case.finalStates
        };

        const numStates = switch(self){
            inline else => |case| case.numStates
        };

        for(0..numStates) |curStateI| {
            const curState:u32 = @truncate(curStateI);

            try writer.print("n{}[label=\"{}\"", .{curState, curState});
            if(finalStates.contains(curState)){
                try writer.print(",shape=doublecircle", .{});
            }
            try writer.print("]; ", .{});

            // TODO could also put the same transitions on the same edge, reduce clutter a bit
            switch(self){
                FiniteAutomaton.dfa => |dfa| {
                    for(dfa.transitions[curState].map.items) |transition| {
                        const range:Pair(u8,u8) = .{transition[1][0], transition[0]};
                        const targetState = transition[1][1];

                        try writer.print("n{} -> n{}[label=\"", .{curState, targetState});
                        try formatTransitionChars(range, writer);
                        try writer.print("\"]; ", .{});
                    }
                },
                FiniteAutomaton.nfa => |nfa| {
                    if(curState > nfa.transitions.len)
                        continue;

                    for(nfa.transitions[curState].map.items) |transitions| {
                        const range:Pair(u8,u8) = .{transitions[1][0], transitions[0]};
                        const targetStates = transitions[1][1];

                        for(targetStates.items) |targetState| {
                            try writer.print("n{} -> n{}[label=\"", .{curState, targetState});
                            try formatTransitionChars(range, writer);
                            try writer.print("\"]; ", .{});
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
    const TransitionsForOneTerminal = Pair(u8, UniqueStateSet);

    const compare = makeOrder(u8);
    const epsilon = 0;
    const EntireTransitionMapOfAState = RangeMap(u8, compare, UniqueStateSet); // eps transitions are represented by a transition char of 0 (not null), as 0 is used as a delimiter in the final machine code compilation anyway, so is not a valid char
    const FinalStates = UniqueStateSet;

    startState:u32,
    // alphabet will be implicit
    numStates:u32,
    transitions:[]EntireTransitionMapOfAState,
    finalStates:FinalStates, 

    internalAllocator:Allocator,

    pub fn init(allocer:Allocator) !@This() {
        const nfa                = RegExNFA{
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
            for(transitionsOfState.map.items) |transition| {
                transition[1][1].deinit();
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

    pub fn addRangeTransitionByState(self:*@This(), state:u32, transition:Pair(u8,u8), targetStates:[]const u32) !void {
        // TODO maybe add a check if this is the simple case of 'insert a single char with a single target without overlap'
        // then this could be the standard 'insert anything' function that calls everything else

        _ = try addRangeTransition(&self.transitions[state], transition, targetStates);
    }

    // splits the given transition map in preparation for the split range to gain new target states (if there is splitting to be done)
    // if the split range is just a single char for instance (-> a split point), this will split any continuous range around the split point into three ranges, so that the upper and lower one can keep their target states, and the split point can have a target state added to it. Thus if the split range is larger, there can be arbitrarily many new ranges, some of which will have not existed before and the state to be added is their first target, others will simply have another target added.
    // returns whether it changed anything
    pub fn addRangeTransition(transitions:*EntireTransitionMapOfAState, splitRange:Pair(u8,u8), newTargetsSlice:anytype) !bool {
        // TODO would giving a choice of allocator make sense here?
        const newTargetStateSet = try UniqueStateSet.initElements(cAllocer, newTargetsSlice);
        // will be cloned for the new ranges, thus we can deinit this later
        defer newTargetStateSet.deinit();
        // constructing this once and cloning is preferable, as this only requires newTargets to be sorted once

        return addRangeTransitionFromStateSet(transitions, splitRange, newTargetStateSet);
    }

    pub fn addRangeTransitionFromStateSet(transitions:*EntireTransitionMapOfAState, splitRange:Pair(u8,u8), newTargetStateSet:UniqueStateSet) !bool {
        // TODO naming: splitRange is also the possible transition chars
        // TODO could be done more efficiently with a 'findOverlappingRangesOrMakeRange' function in the range map, that returns the ranges that overlap with the given range, or creates the range if it doesn't overlap with anything

        // TODO would giving a choice of allocator make sense here?
        var newRangesToInsertLater = try EntireTransitionMapOfAState.initCapacity(cAllocer,4);
        defer newRangesToInsertLater.deinit();

        // split the literal edges, i.e. if an existing range overlaps with either of the splitRange bounds, split it up

        // this is only for iterating over the inner ranges later, but it needs to be adjusted, if the left edge case happens
        var curLowerEdge = splitRange[0];

        // lower bound edge case/overlap:
        if(transitions.findItem(curLowerEdge)) |*lowerEdgeOverlapItem|{
            const range:Pair(u8, u8) = .{lowerEdgeOverlapItem.*[1][0], lowerEdgeOverlapItem.*[0]};
            var targetStates = &lowerEdgeOverlapItem.*[1][1];
            
            // if the lower end of the split range is exactly the lower end of the existing range, we only need to add the new targets to the existing range, the main loop can do that for us
            if(compare(curLowerEdge, range[0]) != Order.eq){
                // we know that the lower end of the split range is strictly higher than the lower end of the existing range, so we need to split the existing range into two
                assert(compare(curLowerEdge, range[0]) == Order.gt, "the lower end of the split range ({?}) has to be strictly higher than the lower end of the existing range ({?}), if it's contained and not equal", .{curLowerEdge, range[0]});

                // insert new lower range (range[0], curLowerEdge - 1), clone the target states from the existing range
                try newRangesToInsertLater.map.insert(.{curLowerEdge - 1, .{range[0], try targetStates.clone()}}, .{.DontSort = true});

                // edit the existing range, and let it get handled again by the main loop
                lowerEdgeOverlapItem.*[1][0] = curLowerEdge;
            }
        }

        var changedSmth = false;

        // now find inner cases (these only need adding to, not splitting)

        // we find the next range that contains something >= curLowerEdge by using the internal map and its find function
        const maybeFirstHigherThanLowerEdge = transitions.map.findSpot(.{curLowerEdge, undefined}, .{});

        var curIndex = 
            if(maybeFirstHigherThanLowerEdge) |firstHigherThanLowerEdge|
                // by subtracting the pointer of the found item from the base pointer, we get 
                // TODO maybe findIndex method
                (@intFromPtr((firstHigherThanLowerEdge.item_ptr)) - @intFromPtr(transitions.map.items.ptr))/@sizeOf(EntireTransitionMapOfAState.Map.Item)
            else
                std.math.maxInt(u32); // in this case, just skip the loop, because the current lower edge is higher than all existing ranges

        // just used to make sure we don't try to add a range above 255 later
        var handled255 = false;

        while(curIndex < transitions.map.items.len) : (curIndex+=1) { // not the only condition, we also break if we've found that the elements were looking at are too high
            var element = &transitions.map.items[curIndex];
            const range:Pair(u8, u8) = .{element[1][0], element[0]};
            var targetStates = &element[1][1];

            if(compare(range[1], splitRange[1]) == Order.gt) {
                // the range ends above the split range:
                // if they don't overlap: just break, we're done

                if(compare(range[0], splitRange[1]) == Order.gt)
                   break;

                // if they do overlap: this is the second edge case -> handle it -> then stop

                // we don't need to concern ourselves with the case where the splitRange[1] == range[1], that can simply be handled in a normal iteration

                // we cannot normally iterate in this case, because the existing range shouldn't be edited in this case. But: in not iterating normally, we could also miss a non-empty lower part of the range. So this edge case can result in 3 ranges in total.
                
                // if there is a lower range, insert it (see normal case below for an explanation of these 2 lines):
                if(compare(curLowerEdge, range[0]) == Order.lt)
                    try newRangesToInsertLater.map.insert(.{range[0] - 1, .{curLowerEdge, try newTargetStateSet.clone()}}, .{.DontSort = true});


                // insert new middle range (range[0], splitRange[1]), clone target states from the existing range, then add the new targets
                const middle = try newRangesToInsertLater.map.insertAndGet(.{splitRange[1], .{range[0], try targetStates.clone()}}, .{.DontSort = true});
                try middle.item_ptr.*[1][1].addAll(newTargetStateSet);

                // edit the existing range to be the upper one, but don't change the target states
                // TODO what about 255?
                element[1][0] = splitRange[1] + 1;

                break;
            }

            // the way we're iterating, the current edge should always be lower than or equal to the range's lower edge
            assert(compare(curLowerEdge, range[0]) != Order.gt, "the current lower edge ({?c}) should always be lower than or equal to the range's lower edge ({?c})", .{curLowerEdge, range[0]});

            // okay we've found two ranges that need to be in the end result: the one that doesn't exist yet: (curLowerEdge, range[0]-1) and the one that does: (range[0], range[1])

            // except: if all of the new targets are already present in the existing range, we don't need to do anything but extend it down to encompass the lower part: (curLowerEdge, range[1])

            try targetStates.ensureUnusedCapacity(newTargetStateSet.items.len);

            // we check whether the new targets are already present and try to add them immediately if they aren't
            var allNewTargetsPresent = true;
            for(newTargetStateSet.items) |newTarget| {
                allNewTargetsPresent = (try targetStates.insertAndGet(newTarget, .{.ReplaceExisting = false, .AssumeCapacity = true})).found_existing and allNewTargetsPresent;
            }

            if(allNewTargetsPresent){
                // set lower to include the new part of the range
                changedSmth = changedSmth or transitions.map.items[curIndex][1][0] != curLowerEdge;

                transitions.map.items[curIndex][1][0] = curLowerEdge;
            }else{
                // if allNewTargetsPresent is false, then one of the insertions above did not find an existing element, so it inserted it, i.e. we changed something
                changedSmth = true;

                // if not all were present, they are now, as we've added them during the search
                // TODO could try out not to add the targets while searching, but just make the new lower range, and `addAll` them, could be faster

                // but we still need to add the lower range in this case (if its not empty)
                // we don't do this immediately, but save it in a list to do it later, so we don't move around the old elements all the time
                if(compare(curLowerEdge, range[0]) == Order.lt)
                    // we simply insert at the end without sorting, because we know that we're getting these ranges in a sorted manner anyway
                    try newRangesToInsertLater.map.insert(.{range[0] - 1, .{curLowerEdge, try newTargetStateSet.clone()}}, .{.DontSort = true});
            }

            // now go on just above the range we handled now, except if we're at the upper edge
            if(range[1] == 255){
                handled255 = true;
                break;
            }

            curLowerEdge = range[1] + 1;
        }

        // if we have iterated through everything, check whether the current lower edge is still below the split range's upper edge, and if so, add the last range
        // but only do this if we're not ad the upper edge: in theory this check would also work for the upper edge, but because a u8 can't hold 256, this check would be wrong, so we handle 255 separately
        if(!handled255 and compare(curLowerEdge, splitRange[1]) != Order.gt)
            try newRangesToInsertLater.map.insert(.{splitRange[1], .{curLowerEdge, try newTargetStateSet.clone()}}, .{.DontSort = true});

        changedSmth = changedSmth or newRangesToInsertLater.map.items.len > 0;

        // now we need to insert the ranges we saved earlier
        try transitions.map.addAll(newRangesToInsertLater.map);

        return changedSmth;

    }

    test "range NFA splitting no edge cases" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(3);

        try nfa.addSingleTransition(0, 'b', 1);
        try nfa.addSingleTransition(0, 'd', 1);

        try nfa.addRangeTransitionByState(0, .{'a', 'e'}, &[_]u32{2});

        // now 'a', 'c', 'e' should lead to 2, 'b', 'd' should lead to 1 and 2
        // and all should be single char ranges
        for(nfa.transitions[0].map.items) |transition| {
            try expect(transition[0]==transition[1][0]);
            const char = transition[0];
            if(char % 2 == 'a' % 2){
                try expect(std.mem.eql(u32, transition[1][1].items, &[_]u32{2}));
            }else{
                try expect(std.mem.eql(u32, transition[1][1].items, &[_]u32{1,2}));
            }
        }
    }

    test "range NFA splitting no edge cases, but empty inner ranges" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(3);

        try nfa.addSingleTransition(0, 'b', 1);
        try nfa.addSingleTransition(0, 'c', 1);

        try nfa.addRangeTransitionByState(0, .{'a', 'e'}, &[_]u32{2});

        try expect(nfa.transitions[0].map.items.len == 4);


        try expect(std.mem.eql(u32, nfa.transitions[0].find('a').?.items, &[_]u32{2}));
        try expect(std.mem.eql(u32, nfa.transitions[0].find('b').?.items, &[_]u32{1,2}));
        try expect(std.mem.eql(u32, nfa.transitions[0].find('c').?.items, &[_]u32{1,2}));
        try expect(std.mem.eql(u32, nfa.transitions[0].find('d').?.items, &[_]u32{2}));
        try expectEqual(nfa.transitions[0].find('d').?.items.ptr, nfa.transitions[0].find('e').?.items.ptr);
    }

    test "range NFA splitting no edge cases, but add existing targets" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(2);

        try nfa.addSingleTransition(0, 'b', 1);

        try nfa.addRangeTransitionByState(0, .{'a', 'e'}, &[_]u32{1});

        try expect(nfa.transitions[0].map.items.len == 2);


        // we expect that we only added a range after all the inner ranges, and extended the existing range to the left
        try expect(std.mem.eql(u32, nfa.transitions[0].find('a').?.items, &[_]u32{1}));
        try expectEqual(nfa.transitions[0].find('a').?.items.ptr, nfa.transitions[0].find('b').?.items.ptr);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('c').?.items, &[_]u32{1}));
        try expectEqual(nfa.transitions[0].find('c').?.items.ptr, nfa.transitions[0].find('d').?.items.ptr);
        try expectEqual(nfa.transitions[0].find('c').?.items.ptr, nfa.transitions[0].find('e').?.items.ptr);
    }

    test "range NFA splitting empty" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(5);

        try nfa.addRangeTransitionByState(0, .{'a', 'e'}, &[_]u32{1});

        try expect(nfa.transitions[0].map.items.len == 1);

        // we expect that we only added a range after all the inner ranges, and extended the existing range to the left
        try expect(std.mem.eql(u32, nfa.transitions[0].find('a').?.items, &[_]u32{1}));
        for('b'..'f') |c| {
            try expectEqual(nfa.transitions[0].find(@intCast(c)).?.items.ptr, nfa.transitions[0].find('a').?.items.ptr);
        }

        try nfa.addRangeTransitionByState(0, .{'f', 'g'}, &[_]u32{2});

        try expect(nfa.transitions[0].map.items.len == 2);

        try nfa.addRangeTransitionByState(0, .{'o', 'x'}, &[_]u32{4});

        try expect(nfa.transitions[0].map.items.len == 3);

        try nfa.addRangeTransitionByState(0, .{'j', 'k'}, &[_]u32{3});

        try expect(nfa.transitions[0].map.items.len == 4);

        const aToE = nfa.transitions[0].map.items[0];
        try expectEqual(aToE[1][0], 'a');
        try expectEqual(aToE[0], 'e');
        try expect(std.mem.eql(u32, aToE[1][1].items, &[_]u32{1}));

        const fToG = nfa.transitions[0].map.items[1];
        try expectEqual(fToG[1][0], 'f');
        try expectEqual(fToG[0], 'g');
        try expect(std.mem.eql(u32, fToG[1][1].items, &[_]u32{2}));

        const jToK = nfa.transitions[0].map.items[2];
        try expectEqual(jToK[1][0], 'j');
        try expectEqual(jToK[0], 'k');
        try expect(std.mem.eql(u32, jToK[1][1].items, &[_]u32{3}));

        const oToX = nfa.transitions[0].map.items[3];
        try expectEqual(oToX[1][0], 'o');
        try expectEqual(oToX[0], 'x');
    }

    test "range NFA splitting lower edge case" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(3);

        try nfa.addRangeTransitionByState(0, .{'a', 'e'}, &[_]u32{1});
        try expectOrSkip(nfa.transitions[0].map.items.len == 1);

        try nfa.addRangeTransitionByState(0, .{'b', 'f'}, &[_]u32{2});

        try expect(nfa.transitions[0].map.items.len == 3);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('a').?.items, &[_]u32{1}));
        try expect(std.mem.eql(u32, nfa.transitions[0].find('b').?.items, &[_]u32{1,2}));
        try expectEqual(nfa.transitions[0].find('b').?.items.ptr, nfa.transitions[0].find('c').?.items.ptr);
        try expectEqual(nfa.transitions[0].find('b').?.items.ptr, nfa.transitions[0].find('d').?.items.ptr);
        try expectEqual(nfa.transitions[0].find('b').?.items.ptr, nfa.transitions[0].find('e').?.items.ptr);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('f').?.items, &[_]u32{2}));
    }

    test "range NFA splitting upper edge case" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(3);

        try nfa.addRangeTransitionByState(0, .{'b', 'f'}, &[_]u32{2});

        try expectOrSkip(nfa.transitions[0].map.items.len == 1);

        try nfa.addRangeTransitionByState(0, .{'a', 'e'}, &[_]u32{1});

        try expect(nfa.transitions[0].map.items.len == 3);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('a').?.items, &[_]u32{1}));
        try expect(std.mem.eql(u32, nfa.transitions[0].find('b').?.items, &[_]u32{1,2}));
        try expectEqual(nfa.transitions[0].find('b').?.items.ptr, nfa.transitions[0].find('c').?.items.ptr);
        try expectEqual(nfa.transitions[0].find('b').?.items.ptr, nfa.transitions[0].find('d').?.items.ptr);
        try expectEqual(nfa.transitions[0].find('b').?.items.ptr, nfa.transitions[0].find('e').?.items.ptr);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('f').?.items, &[_]u32{2}));
    }

    test "range NFA splitting upper and lower edge case" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(3);

        try nfa.addRangeTransitionByState(0, .{'b', 'f'}, &[_]u32{2});

        try expectOrSkip(nfa.transitions[0].map.items.len == 1);

        try nfa.addRangeTransitionByState(0, .{'c', 'e'}, &[_]u32{1});

        try expect(nfa.transitions[0].map.items.len == 3);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('b').?.items, &[_]u32{2}));
        try expect(std.mem.eql(u32, nfa.transitions[0].find('c').?.items, &[_]u32{1,2}));
        try expectEqual(nfa.transitions[0].find('c').?.items.ptr, nfa.transitions[0].find('d').?.items.ptr);
        try expectEqual(nfa.transitions[0].find('c').?.items.ptr, nfa.transitions[0].find('e').?.items.ptr);
        try expect(std.mem.eql(u32, nfa.transitions[0].find('f').?.items, &[_]u32{2}));
    }

    test "range NFA splitting epsilon cases" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var nfa = try RegExNFA.init(arena.allocator());
        defer nfa.deinit();

        try nfa.addStates(3);

        try nfa.addSingleTransition(0, RegExNFA.epsilon, 1);

        try nfa.addRangeTransitionByState(0, .{RegExNFA.epsilon, 'b'}, &[_]u32{2});

        try expect(nfa.transitions[0].map.items.len == 2);

        try expect(std.mem.eql(u32, nfa.transitions[0].find(RegExNFA.epsilon).?.items, &[_]u32{1,2}));
        for(1..'c') |c| {
            try expect(std.mem.eql(u32, nfa.transitions[0].find(@intCast(c)).?.items, &[_]u32{2}));
        }

        var nfa2 = try RegExNFA.init(arena.allocator());
        defer nfa2.deinit();

        try nfa2.addStates(3);

        _ = try nfa2.addRangeTransitionByState(0, .{RegExNFA.epsilon, 'b'}, &[_]u32{1});

        try expectOrSkip(nfa2.transitions[0].map.items.len == 1);

        _ = try nfa2.addRangeTransitionByState(0, .{'a', 'c'}, &[_]u32{2});

        try expect(nfa2.transitions[0].map.items.len == 3);
        try expect(std.mem.eql(u32, nfa2.transitions[0].find(RegExNFA.epsilon).?.items, &[_]u32{1}));
        for(0..'a') |c| {
            try expectEqual(nfa2.transitions[0].find(@intCast(c)).?.items.ptr, nfa2.transitions[0].find(RegExNFA.epsilon).?.items.ptr);
        }

        try expect(std.mem.eql(u32, nfa2.transitions[0].find('a').?.items, &[_]u32{1,2}));
        try expectEqual(nfa2.transitions[0].find(@intCast('a')).?.items.ptr, nfa2.transitions[0].find('b').?.items.ptr);

        try expect(std.mem.eql(u32, nfa2.transitions[0].find('c').?.items, &[_]u32{2}));

        var nfa3 = try RegExNFA.init(arena.allocator());
        defer nfa3.deinit();

        try nfa3.addStates(3);

        _ = try nfa3.addRangeTransitionByState(0, .{RegExNFA.epsilon, 'd'}, &[_]u32{1});

        try expectOrSkip(nfa3.transitions[0].map.items.len == 1);

        _ = try nfa3.addRangeTransitionByState(0, .{'a', 'c'}, &[_]u32{2});

        try expect(nfa3.transitions[0].map.items.len == 3);
        try expect(std.mem.eql(u32, nfa3.transitions[0].find(RegExNFA.epsilon).?.items, &[_]u32{1}));
        for(0..'a') |c| {
            try expectEqual(nfa3.transitions[0].find(@intCast(c)).?.items.ptr, nfa3.transitions[0].find(RegExNFA.epsilon).?.items.ptr);
        }

        try expect(std.mem.eql(u32, nfa3.transitions[0].find('a').?.items, &[_]u32{1,2}));
        try expectEqual(nfa3.transitions[0].find(@intCast('a')).?.items.ptr, nfa3.transitions[0].find('b').?.items.ptr);
        try expectEqual(nfa3.transitions[0].find(@intCast('a')).?.items.ptr, nfa3.transitions[0].find('c').?.items.ptr);

        try expect(std.mem.eql(u32, nfa3.transitions[0].find('d').?.items, &[_]u32{1}));
    }

    fn debugLogTransitions(self:@This()) void {
        for(0.., self.transitions) |i, transitionMap| {
            debugLog("state {}:", .{i});
            for(transitionMap.map.items) |transition| {
                const upper = transition[0];
                const lower = transition[1][0];
                std.debug.print("    [", .{});
                if(lower == epsilon){
                    std.debug.print("ε-", .{});
                }else{
                    std.debug.print("{c}-", .{lower});
                }
                if(upper == epsilon){
                    std.debug.print("ε", .{});
                }else{
                    std.debug.print("{c}", .{upper});
                }
                std.debug.print("] to {{", .{});
                for(transition[1][1].items) |target| {
                    std.debug.print("{} ", .{target});
                }
                std.debug.print("}}\n", .{});
            }
        }
    }


    pub fn addSingleTransition(self:*@This(), from:u32, with:u8, to:u32) !void {
        // for range based transitions, this needs to check if the transition exists and if it does but with a different target state, split up the ranges of the transitions etc.
        // this is the simple case, where we're only adding a single char transition, so there is a maximum of three ranges to consider

        var transitions = &self.transitions[from];

        var entry = try transitions.findOrMakeSpot(with, .{});
        if(!entry.found_existing){
            // simple, just add the transition, there is no range overlap to split

            // set the char, if its new
            entry.setRange(with, with);
            entry.value().* = try UniqueStateSet.initElements(self.internalAllocator, &[1]u32{to});
        }else{
            _ = try addRangeTransition(transitions, .{with, with}, &[1]u32{to});
        }
    }

    // returns whether it added anything
    pub fn addAllTransitions(transitionsToCopyTo:*EntireTransitionMapOfAState, transitionsToCopyFrom:EntireTransitionMapOfAState, comptime opts:struct{excludeEpsilonTransitions:bool = false}) !bool {
        if(transitionsToCopyTo.map.items.ptr == transitionsToCopyFrom.map.items.ptr){
            return false;
        }

        var addedSomething = false;
        for(transitionsToCopyFrom.map.items) |transition| {
            var fromRange:Pair(u8,u8) = .{transition[1][0], transition[0]};

            if(opts.excludeEpsilonTransitions and fromRange[0] == epsilon){
                if(fromRange[1] == epsilon)
                    continue;

                // otherwise, the range includes non-epsilon transitions, so we add that part
                // TODO honestly those ranges don't make a whole lot of sense, as few strings will include '\1' and so on
                fromRange[0] = epsilon + 1;
            }

            if(transition[0] == epsilon)
                continue;

            // be careful not to do addedSomething = addedSomething or ... because the or is short circuiting, so its not actually equivalent to doing something like addedSomething |= ... in C...
            addedSomething = try addRangeTransitionFromStateSet(transitionsToCopyTo, .{transition[1][0], transition[0]}, transition[1][1]) or addedSomething;
        }
        return addedSomething;
    }

    // does not eliminate, but 'fill' epsilon transitions, so that they can be ignored from now on (because the language of the NFA after this function is the same with or without them)
    pub fn backUpEpsTransitions(self:*@This()) !void {
        // TODO this is obviously very inefficient, I'm thinking about how to do it better, maybe a kind of modified post order traversal (that takes cycles into consideration)

        // to handle transitive epsilons: just do this as long as it adds anything (this is why its inefficient)
        var changedSmth = true;
        while(changedSmth){
            changedSmth = false;
            for(0.., self.transitions) |state,*transitionsFromState| {
                if(transitionsFromState.find(epsilon)) |epsTargetsFromState| {
                    // solution: copy all transitions of the targeted states (epsTargetsFromState) to the current state
                    // also if the target is a final state, make this one final too
                    for(epsTargetsFromState.items) |epsTargetState|{
                        // exclude eps transitions here, they just make the whole thing bigger, and adding them anywhere might modify the epsTargetsFromState while we're iterating over them.
                        if(try addAllTransitions(&self.transitions[state], self.transitions[epsTargetState], .{.excludeEpsilonTransitions = true}))
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
    // if called without options, this function just uses the NFAs allocator for the DFA, i.e. that allocators lifetime has to exceed the lifetime of the DFA
    pub fn toPowersetConstructedDFA(self:*@This(), opts:struct{overrideAllocator:?Allocator = null}) !RegExDFA{
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
        
        var dfa = try RegExDFA.init(opts.overrideAllocator orelse self.internalAllocator);
        // worklist of nfa (and generated i.e. powerset-) states to visit
        var worklist = try std.ArrayList(UniqueStateSet).initCapacity(self.internalAllocator, 8);

        // add start state to new DFA
        dfa.startState = try dfa.addState();
        const startStateSet = try UniqueStateSet.initElements(dfa.internalAllocator, &[1]u32{self.startState});
        try nfaToDfaStates.putNoClobber(startStateSet.items, dfa.startState);

        // used like a stack
        try worklist.append(startStateSet);

        // TODO 'curNfaState(s)' is not named perfectly, because it can also be a 'powerset state' that doesnt exist in the original NFA, just implicitly
        while(worklist.popOrNull()) |curNfaStates| {
            // get the state, has to be in there (but not visited yet) if its in the worklist
            const curDfaState = nfaToDfaStates.get(curNfaStates.items).?;

            // go through the transitions of the states, and construct a transition map for the state step by step
            // after the transition map is complete, the actual dfa states can be created and the dfa transitions can be added
            var combinedTransitionsForCurNfaState = try EntireTransitionMapOfAState.init(self.internalAllocator);
            // the transition lists in here are kept sorted, for deduplication (as they represent sets)

            var madeFinalAlready = false;

            for(curNfaStates.items) |curNfaState| {
                assert(self.transitions.len > curNfaState, "nfa state out of bounds, nfa is invalid", .{});

                // if any of the current nfa states is final, make the dfa state final
                if(!madeFinalAlready and self.finalStates.contains(curNfaState)){
                    try dfa.designateStatesFinal(&[1]u32{@truncate(curDfaState)});
                    madeFinalAlready = true;
                }

                _ = try addAllTransitions(&combinedTransitionsForCurNfaState, self.transitions[curNfaState], .{.excludeEpsilonTransitions = true});
            }

            // now we have the combined transitions for the current state, so we can create the actual states and add the transitions in the dfa

            for(combinedTransitionsForCurNfaState.map.items) |transition| {
                const targetStates = transition[1][1];

                // create or get state
                const targetStateEntry = try nfaToDfaStates.getOrPut(targetStates.items);
                if(!targetStateEntry.found_existing){
                    targetStateEntry.value_ptr.* = try dfa.addState();

                    // add (the possibly combined state of the nfa) to worklist, because its new -> we haven't visited it yet
                    try worklist.append(targetStates);
                }

                // add transition
                try dfa.transitions[curDfaState].insert(transition[1][0], transition[0], targetStateEntry.value_ptr.*, .{.AssumeNoOverlap = true});
            }

        }

        return dfa;
    }
};

pub fn compileInputStringAnyWriter(arena:*std.heap.ArenaAllocator, input: []const u8, writer:anytype) !RegExDFA.CompiledRegExDFA {
    // TODO resource management of the diag doesn't work properly
    var diag = Diag.init(arena.allocator());
    defer diag.deinit();

    var tok = try Tokenizer.init(arena.allocator(), input, &diag);
    defer tok.deinit();

    var parser = Parser.init(arena.allocator(), &tok);

    const regex = parser.parseExpr(0) catch |e| {
        // rethrow out of memory
        if(e == error.OutOfMemory){
            return error.OutOfMemory;
        }

        try diag.printAll(writer, input);
        return e;
    };

    var dfa = try regex.toDFA(.{});

    return dfa.compile(arena, false, .{});
}

pub fn compileInputString(arena:*std.heap.ArenaAllocator, input: []const u8, comptime comptime_opts:struct{printErrors:bool = true}) !RegExDFA.CompiledRegExDFA {
    return compileInputStringAnyWriter(arena, input, if(comptime_opts.printErrors) std.io.getStdErr().writer() else std.io.null_writer());
}

fn eqlPairU8(a: Pair(u8,u8), b: Pair(u8,u8)) bool {
    return a[0] == b[0] and a[1] == b[1];
}

var emptyTestingDiag = Diag.init(std.heap.c_allocator);
const emptyTestingDiagPtr = &emptyTestingDiag;

test "tokenizer" {
    const input = "xyz|w*(abc)*de*f";
    var tok = try Tokenizer.init(std.testing.allocator, input, emptyTestingDiagPtr);
    defer tok.deinit();
    const buf = try tok.debugFmt();
    try expect(std.mem.eql(u8, buf.items, "x y z|w* (a b c)* d e* f"));
}

fn expectLiteralChar(token:Token, expected:u8) anyerror!void {
    try expectEqual(.Char, token.kind);
    try expectEqual(expected, token.char);
}


test "tokenizer syntactic sugar" {
    const input = "xyz|w+(abc)?de*f";
    var tok = try Tokenizer.init(std.testing.allocator, input, emptyTestingDiagPtr);
    defer tok.deinit();
    const buf = try tok.debugFmt();
    try expect(std.mem.eql(u8, buf.items, "x y z|w+ (a b c)? d e* f"));
}

test "tokenizer char groups" {
    const input = "[xyz]|[a-f]";
    var tok = try Tokenizer.init(std.testing.allocator, input, emptyTestingDiagPtr);
    defer tok.deinit();
    const buf = try tok.debugFmt();
    try expect(std.mem.eql(u8, buf.items, "[xyz]|[a-f]"));

    const input2 = "a-^b";
    var tok2 = try Tokenizer.init(std.testing.allocator, input2, emptyTestingDiagPtr);
    defer tok2.deinit();

    var i:u32 = 0;
    while(tok2.nextOrNull()) |token| {
        try expect(token.kind == Token.Kind.Char or token.kind == Token.Kind.Concat);

        if(token.kind == Token.Kind.Char){
            try expectEqual(input2[i], token.char);
            i += 1;
        }
    }

    // shouldn't need to escape additional ] outside of a char group
    const input3 = "a]";
    var tok3 = try Tokenizer.init(std.testing.allocator, input3, emptyTestingDiagPtr);
    defer tok3.deinit();
    try expectLiteralChar(tok3.nextAssume(), 'a');
    try expectEqual(.Concat, tok3.nextAssume().kind);
    try expectLiteralChar(tok3.nextAssume(), ']');
    try expectEqual(null,tok3.nextOrNull());

    // outside of a char group, - and ^ should be literal
    const input4 = "^a-bc";
    var tok4 = try Tokenizer.init(std.testing.allocator, input4, emptyTestingDiagPtr);
    defer tok4.deinit();
    i = 0;
    while(tok4.nextOrNull()) |token| {
        try expect(token.kind == Token.Kind.Char or token.kind == Token.Kind.Concat);

        if(token.kind == Token.Kind.Char){
            try expectEqual(input4[i],token.char);
            i += 1;
        }
    }
}

test "tokenizer escaping" {
    // the spaces separate the special cases to be tested
    const input1 = " \\| \\\\ \\[ \\] ";
    var tok1 = try Tokenizer.init(std.testing.allocator, input1, emptyTestingDiagPtr);
    defer tok1.deinit();

    while(tok1.nextOrNull()) |token| {
        // because of the escaping, everything should be literal (concatenated together)
        try expect(token.kind == Token.Kind.Char or token.kind == Token.Kind.Concat);
    }

    // now test it inside a char group
    const input2 = "[a\\-z]";
    var tok2 = try Tokenizer.init(std.testing.allocator, input2, emptyTestingDiagPtr);
    defer tok2.deinit();

    try expect(tok2.nextAssume().kind == Token.Kind.LSquareBrack);
    try expectLiteralChar(tok2.nextAssume(), 'a');
    try expectLiteralChar(tok2.nextAssume(), '-');
    try expectLiteralChar(tok2.nextAssume(), 'z');
    try expect(tok2.nextAssume().kind == Token.Kind.RSquareBrack);
    try expectEqual(null, tok2.nextOrNull());

    // wrong escape
    const input3 = "[a\\";
    try expect(Tokenizer.init(std.testing.allocator, input3, emptyTestingDiagPtr) == SyntaxError.PrematureEnd);
}

test "parsing edge cases" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // test the manual way of tokenizing+parsing
    const input1 = "a|";
    var diag = Diag.init(arena.allocator());
    var tok1 = try Tokenizer.init(std.testing.allocator, input1, &diag);
    defer tok1.deinit();
    // use arena to prevent leak
    var parser = Parser.init(arena.allocator(), &tok1);
    try expectAnyError(parser.parseExpr(0));

    const input2 = "a|b|c";
    const regex = try Parser.parseNoDiagnostic(std.testing.allocator, input2);
    defer regex.deinit();

    try expectEqual(.Union, regex.kind);

    const a:Pair(u8, u8) = .{'a', 'a'};
    const b:Pair(u8, u8) = .{'b', 'b'};
    const c:Pair(u8, u8) = .{'c', 'c'};

    if(regex.left.?.kind == Token.Kind.Union){
        try expect(regex.left.?.left.?.kind == Token.Kind.Char);
        try expectEqualDeep(regex.left.?.left.?.chars, a);
        try expect(regex.left.?.right.?.kind == Token.Kind.Char);
        try expectEqualDeep(regex.left.?.right.?.chars, b);

        try expect(regex.right.?.kind == Token.Kind.Char);
        try expectEqualDeep(regex.right.?.chars, c);
    }else{
        try expect(regex.left.?.kind == Token.Kind.Char);
        try expectEqualDeep(regex.left.?.chars, a);

        try expect(regex.right.?.kind == Token.Kind.Union); 
        try expect(regex.right.?.left.?.kind == Token.Kind.Char);
        try expectEqualDeep(regex.right.?.left.?.chars, b);
        try expect(regex.right.?.right.?.kind == Token.Kind.Char);
        try expectEqualDeep(regex.right.?.right.?.chars, c);
    }

    const input3 = "[b-";
    try expectParserError(SyntaxError.PrematureEnd, Parser.parse(std.testing.allocator, input3));

    const input4 = "[b-]";
    try expectParserError(SyntaxError.InvalidToken, Parser.parse(std.testing.allocator, input4));

    const input5 = "[b-a]";
    try expectParserError(ParseError.SemanticallyInvalidRange, Parser.parse(std.testing.allocator, input5));

    const input6 = "[]";
    const regex6 = try Parser.parseNoDiagnostic(std.testing.allocator, input6);
    defer regex6.deinit();
    try expect(regex6.kind == Token.Kind.Char);
    try expect(regex6.chars[0] == RegExNFA.epsilon);
    try expect(regex6.chars[1] == RegExNFA.epsilon);
    try expect(regex6.left == null);
    try expect(regex6.right == null);

    // invert edge cases
    const input7 = "[^\x01-\xff]";
    const regex7 = try Parser.parseNoDiagnostic(std.testing.allocator, input7);
    defer regex7.deinit();

    try expect(regex7.kind == Token.Kind.Char);
    try expect(regex7.chars[0] == RegExNFA.epsilon);
    try expect(regex7.chars[1] == RegExNFA.epsilon);
}

test "parsing error messages" {
  var list = std.ArrayList(u8).init(std.testing.allocator);
  defer list.deinit();
  var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
  defer arena.deinit();

  const expectErrorCaretPosition = struct {
    fn f(l: anytype, comptime position:comptime_int, comptime length:comptime_int) !void {
      try expect(std.mem.containsAtLeast(u8, l.items, 1, "\n" ++ " " ** position));
      try expect(std.mem.count(u8, l.items, "\n" ++ " " ** (position + 1)) == 0);
      try expect(std.mem.containsAtLeast(u8, l.items, 1, "^" ++ "~" ** (length-1)));
    }
  }.f;

  const input1 = "a|||";
  try expectAnyError(compileInputStringAnyWriter(&arena, input1, list.writer()));

  // assert that the error message contains the correct message and indentation/position
  try expect(std.mem.containsAtLeast(u8, list.items, 1, "invalid token"));
  try expectErrorCaretPosition(list, 2, 1);

  list.clearRetainingCapacity();

  const input2 = "a|";
  try expectAnyError(compileInputStringAnyWriter(&arena, input2, list.writer()));

  try expect(std.mem.containsAtLeast(u8, list.items, 1, "premature"));
  try expectErrorCaretPosition(list, 2, 1);

  const input3 = "a|b|";
  try expectAnyError(compileInputStringAnyWriter(&arena, input3, list.writer()));

  try expect(std.mem.containsAtLeast(u8, list.items, 1, "premature"));
  try expectErrorCaretPosition(list, 4, 1);

  list.clearRetainingCapacity();
  const input4 = "[z-y]"; // missing closing bracket
  try expectAnyError(compileInputStringAnyWriter(&arena, input4, list.writer()));

  try expect(std.mem.containsAtLeast(u8, list.items, 1, "semantically invalid range"));
  try expectErrorCaretPosition(list, 1, 3);

  list.clearRetainingCapacity();
  const input5 = ""; // empty input
  try expectAnyError(compileInputStringAnyWriter(&arena, input5, list.writer()));

  try expect(std.mem.containsAtLeast(u8, list.items, 1, "premature"));
}


test "parsing char groups" {
    const input1 = "[aceg]";
    const regex = try Parser.parseNoDiagnostic(std.testing.allocator, input1);
    defer regex.deinit();

    const isOnlyCharGroup = struct{
        fn f(r:*RegEx, isLeaf:bool, _:usize) anyerror!void {
            try expect(!isLeaf == r.isOperator());
            if(isLeaf){
                try expect(r.kind == Token.Kind.Char);
            }else{
                try expect(r.kind == Token.Kind.Union);
                _ = try expectNotNull(r.left);
                _ = try expectNotNull(r.right);
            }
        }
    }.f;

    try regex.traverse(struct{
        fn f(r:*RegEx, isLeaf:bool, depth:usize) anyerror!void {
            try isOnlyCharGroup(r, isLeaf, depth);
            if(isLeaf)
                try expect(depth == 2);
        }
    }.f);

    const input2 = "[a-d]";
    const regex2 = try Parser.parseNoDiagnostic(std.testing.allocator, input2);
    defer regex2.deinit();

    try expect(regex2.kind == Token.Kind.Char);
    try expect(regex2.chars[0] == 'a');
    try expect(regex2.chars[1] == 'd');
    try expect(regex2.left == null);
    try expect(regex2.right == null);


    const complicatedRangeInput = "jjhejdjcjbjgjf-gje-gj";
    const input3 = "[" ++ complicatedRangeInput ++ "]";
    const regex3 = try Parser.parseNoDiagnostic(std.testing.allocator, input3);
    defer regex3.deinit();

    // should just be one union between b-h and j
    try expect(regex3.kind == .Union);
    try expect(regex3.left.?.kind == .Char);
    try expect(regex3.right.?.kind == .Char);

    const options3 = &[_]Pair(u8,u8){
        .{'b', 'h'},
        .{'j', 'j'},
    };

    inline for(options3) |option| {
        try expect(
            eqlPairU8(regex3.left.?.chars, option)
            or
            eqlPairU8(regex3.right.?.chars, option)
        );
    }

    // now the same thing, but inverted
    const input4 = "[^" ++ complicatedRangeInput ++ "]";
    const regex4 = try Parser.parseNoDiagnostic(std.testing.allocator, input4);
    defer regex4.deinit();
    
    const options4 = &[_]Pair(u8,u8){
        .{1, 'a'},
        .{'i', 'i'},
        .{'k', 255},
    };

    inline for(options4) |option| {
        if(regex4.left.?.kind == .Char){
            try expect(
                eqlPairU8(regex4.left.?.chars, option)
                or
                eqlPairU8(regex4.right.?.left.?.chars, option)
                or
                eqlPairU8(regex4.right.?.right.?.chars, option)
            );
        }else{
            try expect(
                eqlPairU8(regex4.right.?.chars, option)
                or
                eqlPairU8(regex4.left.?.left.?.chars, option)
                or
                eqlPairU8(regex4.left.?.right.?.chars, option)
            );
        }
    }

    const input5 = "[a-d]|e|[b-falzxk]";
    const regex5 = try Parser.parseNoDiagnostic(std.testing.allocator, input5);
    defer regex5.deinit();
    try regex5.traverse(isOnlyCharGroup);
}

test "parsing sugar: +" {
    var regex = try Parser.parseNoDiagnostic(std.testing.allocator, "a+");
    defer regex.deinit();

    try expect(regex.kind == Token.Kind.Concat);
    try expect(regex.left.?.kind == Token.Kind.Char);
    try expectEqualDeep(regex.left.?.chars, .{'a', 'a'});
    try expect(regex.right.?.kind == Token.Kind.Kleen);
    try expect(regex.right.?.left.?.kind == Token.Kind.Char);
    try expectEqualDeep(regex.right.?.left.?.chars, .{'a', 'a'});
}

test "parsing sugar: ?" {
    const regex = try Parser.parseNoDiagnostic(std.testing.allocator, "a?");
    defer regex.deinit();

    const comparison = try Parser.parseNoDiagnostic(std.testing.allocator, "a|[]");
    defer comparison.deinit();
    try expectEqualDeep(regex, comparison);
}

test "ab* DFA" {
    var dfa = try RegExDFA.init(std.testing.allocator);
    defer dfa.deinit();

    try dfa.addStates(2);
    const a = 0;
    const b = 1;

    try dfa.transitions[a].insertSingle('a', b, .{});
    try dfa.transitions[b].insertSingle('b', b, .{});
    try dfa.designateStatesFinal(&[1]u32{b});

    try expect(dfa.isInLanguageInterpreted("a"));
    try expect(dfa.isInLanguageInterpreted("ab"));
    try expect(dfa.isInLanguageInterpreted("abb"));
    try expect(dfa.isInLanguageInterpreted("abbbbbbbbbbbbbbbbbbbbbbbbbb"));
    try expect(!dfa.isInLanguageInterpreted("b"));
    try expect(!dfa.isInLanguageInterpreted("ba"));
    try expect(!dfa.isInLanguageInterpreted("aba"));
    try expect(!dfa.isInLanguageInterpreted("abbbbbbbbbbbbbbbbbbbbbbbbbba"));
}

test "ab|aaa NFA" {
    var nfa = try RegExNFA.init(std.testing.allocator);
    defer nfa.deinit();

    try nfa.addStates(6);
    try nfa.addSingleTransition(0, 'a', 1);
    try expect(nfa.transitions[0].find('a') != null);
    try expect(nfa.transitions[0].find('a').?.items[0] == 1);
    try expect(nfa.transitions[0].valueByIndex(0).items[0] == 1);
    try expect(nfa.transitions[0].find('b') == null);

    try nfa.addSingleTransition(0, 'a', 2);
    try nfa.addSingleTransition(1, 'b', 3);
    try nfa.addSingleTransition(2, 'a', 4);
    try nfa.addSingleTransition(4, 'a', 5);
    try nfa.designateStatesFinal(&[_]u32{3,5});

    try expect(std.mem.eql(u32, nfa.transitions[0].find('a').?.items, &[2]u32{1,2}));
}

test "NFA eps removal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(2);
    try nfa.addSingleTransition(0, RegExNFA.epsilon, 1);
    try nfa.addSingleTransition(1, 'a', 1);
    try nfa.designateStatesFinal(&[_]u32{1});

    try expect(!nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].find('a') == null);

    try nfa.backUpEpsTransitions();

    try expect(nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].find('a') != null);
    try expect((nfa.transitions[0].find('a').?).items[0] == 1);
}

test "NFA transitive eps removal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(3);
    try nfa.addSingleTransition(0, RegExNFA.epsilon, 1);
    try nfa.addSingleTransition(1, RegExNFA.epsilon, 2);
    try nfa.addSingleTransition(2, 'a', 2);
    try nfa.designateStatesFinal(&[_]u32{2});

    try expect(!nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].find('a') == null);

    try nfa.backUpEpsTransitions();

    try expect(nfa.finalStates.contains(0));
    try expect(nfa.transitions[0].find('a') != null);
    try expect(nfa.transitions[0].find('a').?.items[0] == 2);

    var nfa2 = try RegExNFA.init(arena.allocator());
    try nfa2.addStates(3);
    try nfa2.addSingleTransition(0, RegExNFA.epsilon, 1);
    try nfa2.addSingleTransition(1, RegExNFA.epsilon, 2);
    try nfa2.addSingleTransition(2, 'a', 2);

    try expect(nfa2.transitions[0].find('a') == null);

    try nfa2.backUpEpsTransitions();

    try expect(nfa2.transitions[0].find('a') != null);
    try expect(nfa2.transitions[0].find('a').?.items[0] == 2);


}

test "NFA simple powerset construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(6);
    try nfa.addSingleTransition(0, 'a', 1);
    try nfa.addSingleTransition(0, 'a', 2);
    try nfa.addSingleTransition(1, 'b', 3);
    try nfa.addSingleTransition(2, 'a', 4);
    try nfa.addSingleTransition(4, 'a', 5);
    try nfa.designateStatesFinal(&[_]u32{3,5});

    var dfa = try nfa.toPowersetConstructedDFA(.{});
    try expect(dfa.isInLanguageInterpreted("ab"));
    try expect(dfa.isInLanguageInterpreted("aaa"));

    // nothing else should be in the language
    // lets just test a bunch of random strings

    var rnd = std.rand.DefaultPrng.init(0);
    for(0..10000) |_| {
        const length = rnd.random().int(u8);
        const buf = try std.testing.allocator.allocSentinel(u8, length, 0);
        defer std.testing.allocator.free(buf);
        for(buf) |*c| {
            c.* = rnd.random().int(u8);
        }
        try expect(!dfa.isInLanguageInterpreted(buf));
    }
}

test "complex eps-NFA powerset construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(4);
    try nfa.addSingleTransition(0, RegExNFA.epsilon, 2);
    try nfa.addSingleTransition(0, 'a', 1);
    try nfa.addSingleTransition(1, 'b', 1);
    try nfa.addSingleTransition(2, 'c', 1);
    try nfa.addSingleTransition(2, 'd', 3);
    try nfa.addSingleTransition(2, 'd', 1);
    try nfa.addSingleTransition(1, 'e', 0);
    try nfa.addSingleTransition(1, 'e', 3);
    try nfa.addSingleTransition(3, RegExNFA.epsilon, 1);

    try nfa.designateStatesFinal(&[_]u32{3});

    try nfa.backUpEpsTransitions();
    var dfa = try nfa.toPowersetConstructedDFA(.{});
    try expect(dfa.isInLanguageInterpreted("abed"));
    try expect(dfa.isInLanguageInterpreted("abbbbbed"));
    try expect(dfa.isInLanguageInterpreted("dbbbbbeceecebbbed"));
}

test "xyz|w*(abc)*de*f regex to dfa compiled" {
    const input = "xyz|w*(abc)*de*f";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);
    try expect(regex.internalAllocator.ptr == arena.allocator().ptr);

    var dfa = try regex.toDFA(.{});
    try expect(dfa.internalAllocator.ptr == arena.allocator().ptr);

    const compiledDFA = try dfa.compile(&arena, false, .{});

    const xyzTestCases = struct{
        fn xyzTestCases(ddfa:anytype, checkFn:anytype) !void {
            try expect(checkFn(ddfa, "xyz"));

            try expect(!checkFn(ddfa, "xz"));
            try expect(!checkFn(ddfa, "xy"));
            try expect(!checkFn(ddfa, "x"));
            try expect(!checkFn(ddfa, "y"));
            try expect(!checkFn(ddfa, "z"));

            try expect(checkFn(ddfa, "wwwwwwwwdf"));
            try expect(checkFn(ddfa, "df"));
            try expect(checkFn(ddfa, "deef"));
            try expect(checkFn(ddfa, "wabcabcdeeef"));
            try expect(checkFn(ddfa, "wwwwabcabcabcdeeef"));

            try expect(!checkFn(ddfa, "wwwwacabcabcdeeef"));
            try expect(!checkFn(ddfa, "xyz" ++ "wwwwwwwwdf"));
            try expect(!checkFn(ddfa, "xyz" ++ "df"));
            try expect(!checkFn(ddfa, "xyz" ++ "wabcabcdeeef"));
            try expect(!checkFn(ddfa, "xyz" ++ "wwwwabcabcabcdeeef"));
        }
    }.xyzTestCases;

    try xyzTestCases(dfa, RegExDFA.isInLanguageInterpreted);
    try xyzTestCases(compiledDFA, RegExDFA.CompiledRegExDFA.isInLanguageCompiled);
}

test "x[yz]|[.]w*([a-c])*de*[f-i] regex to dfa compiled" {
    const input = "x[yz]|[.]w*([a-c])*de*[f-i]";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);
    try expect(regex.internalAllocator.ptr == arena.allocator().ptr);

    var dfa = try regex.toDFA(.{});
    try expect(dfa.internalAllocator.ptr == arena.allocator().ptr);

    var compiledDFA = try dfa.compile(&arena, false, .{});

    
    try expect(compiledDFA.isInLanguageCompiled("xz"));
    try expect(compiledDFA.isInLanguageCompiled("xy"));
    try expect(!compiledDFA.isInLanguageCompiled("xyz"));
    try expect(!compiledDFA.isInLanguageCompiled("y"));
    try expect(!compiledDFA.isInLanguageCompiled("z"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdg"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeeg"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeei"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeef"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeefi"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeefig"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdfig"));
}

test "simple anychar" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const input1 = ".";

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input1);

    var dfa = try regex.toDFA(.{});

    var compiledDFA = try dfa.compile(&arena, false, .{});

    for(1..255) |c| {
        const input:[:0]const u8 = &[1:0]u8{@intCast(c)};
        try expect(compiledDFA.isInLanguageCompiled(input));
        try expect(dfa.isInLanguageInterpreted(input));
    }

    const input2 = ".a|..";

    const regex2 = try Parser.parseNoDiagnostic(arena.allocator(), input2);

    var dfa2 = try regex2.toDFA(.{});

    var compiledDFA2 = try dfa2.compile(&arena, false, .{});

    for(1..255) |c1| {
        for(1..255) |c2| {
            const input:[:0]const u8 = &[2:0]u8{@intCast(c1), @intCast(c2)};
            try expect(compiledDFA2.isInLanguageCompiled(input));
            try expect(dfa2.isInLanguageInterpreted(input));
        }
    }

    const input3 = "a|.|[b-f]";

    const regex3 = try Parser.parseNoDiagnostic(arena.allocator(), input3);

    var dfa3 = try regex3.toDFA(.{});

    var compiledDFA3 = try dfa3.compile(&arena, false, .{});

    for(1..255) |c| {
        const input:[:0]const u8 = &[1:0]u8{@intCast(c)};
        try expect(compiledDFA3.isInLanguageCompiled(input));
        try expect(dfa3.isInLanguageInterpreted(input));
    }
}

test "x[yz]|.w*([a-c])*.e*[f-i] regex to dfa compiled" {
    const input = "x[yz]|.w*([a-c])*.e*[f-i]";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);
    try expect(regex.internalAllocator.ptr == arena.allocator().ptr);

    var dfa = try regex.toDFA(.{});
    try expect(dfa.internalAllocator.ptr == arena.allocator().ptr);

    var compiledDFA = try dfa.compile(&arena, false, .{});


    try expect(compiledDFA.isInLanguageCompiled("xz"));
    try expect(compiledDFA.isInLanguageCompiled("xy"));
    try expect(!compiledDFA.isInLanguageCompiled("xyz"));
    try expect(!compiledDFA.isInLanguageCompiled("y"));
    try expect(!compiledDFA.isInLanguageCompiled("z"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdg"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeeg"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeei"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeef"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabeeef"));
    try expect(compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabf"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcafe"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeefi"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdeefig"));
    try expect(!compiledDFA.isInLanguageCompiled(".abcaaaaccbbcabccbabbcabcabacbbcabdfig"));
}

test "x?[yz]+|.?w+ regex to dfa compiled" {
    const input = "x?[yzyz]+|.?w+"; // duplicates on purpose

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);
    try expect(regex.internalAllocator.ptr == arena.allocator().ptr);

    var dfa = try regex.toDFA(.{});
    try expect(dfa.internalAllocator.ptr == arena.allocator().ptr);

    var compiledDFA = try dfa.compile(&arena, false, .{});


    try expect(compiledDFA.isInLanguageCompiled("xz"));
    try expect(compiledDFA.isInLanguageCompiled("xy"));
    try expect(compiledDFA.isInLanguageCompiled("y"));
    try expect(compiledDFA.isInLanguageCompiled("z"));
    try expect(compiledDFA.isInLanguageCompiled("xyz"));
    try expect(!compiledDFA.isInLanguageCompiled("x"));

    try expect(!compiledDFA.isInLanguageCompiled(""));

    try expect(compiledDFA.isInLanguageCompiled("\x02wwww"));
    try expect(compiledDFA.isInLanguageCompiled("aw"));
    try expect(compiledDFA.isInLanguageCompiled("w"));
}

test "eps-only/empty string regex" {
    const input = "[]";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);
    try expect(regex.internalAllocator.ptr == arena.allocator().ptr);

    try expect(regex.kind == Token.Kind.Char);
    try expect(regex.chars[0] == RegExNFA.epsilon);
    try expect(regex.chars[1] == RegExNFA.epsilon);

    var dfa = try regex.toDFA(.{});
    try expect(dfa.internalAllocator.ptr == arena.allocator().ptr);

    var compiledDFA = try dfa.compile(&arena, false, .{});

    try expect(dfa.isInLanguageInterpreted(""));
    try expect(compiledDFA.isInLanguageCompiled(""));
    for(1..255) |c| {
        const str:[:0]const u8 = &[_:0]u8{@intCast(c)};
        try expect(!dfa.isInLanguageInterpreted(str));
        try expect(!compiledDFA.isInLanguageCompiled(str));
    }
}

test "single char regex to dfa" {
    const input1 = "x";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input1);
    try expect(regex.internalAllocator.ptr == arena.allocator().ptr);

    var dfa = try regex.toDFA(.{});
    try expect(dfa.internalAllocator.ptr == arena.allocator().ptr);

    var compiledDFA = try dfa.compile(&arena, false, .{});

    try expect(compiledDFA.isInLanguageCompiled("x"));
    try expect(dfa.isInLanguageInterpreted("x"));

    try expect(!compiledDFA.isInLanguageCompiled(""));
    try expect(!dfa.isInLanguageInterpreted(""));
    try expect(!compiledDFA.isInLanguageCompiled("y"));
    try expect(!dfa.isInLanguageInterpreted("y"));
    try expect(!compiledDFA.isInLanguageCompiled("w"));
    try expect(!dfa.isInLanguageInterpreted("w"));

    // now with ranges
    const input2 = "[b-f]";
    compiledDFA = try compileInputString(&arena, input2, .{});

    try expect(!compiledDFA.isInLanguageCompiled("a"));
    try expect(compiledDFA.isInLanguageCompiled("b"));
    try expect(compiledDFA.isInLanguageCompiled("c"));
    try expect(compiledDFA.isInLanguageCompiled("d"));
    try expect(compiledDFA.isInLanguageCompiled("e"));
    try expect(compiledDFA.isInLanguageCompiled("f"));
    try expect(!compiledDFA.isInLanguageCompiled("g"));

    // now with ranges that include eps
    const input3 = "[\x00-x]";
    dfa = try (try Parser.parseNoDiagnostic(arena.allocator(), input3)).toDFA(.{});

    // compile anew
    compiledDFA = try dfa.compile(&arena, false, .{});
    try expect(compiledDFA.isInLanguageCompiled(""));
    for(1..'x') |c| {
        const str:[:0]const u8 = &[_:0]u8{@intCast(c)};
        try expect(compiledDFA.isInLanguageCompiled(str));
    }
    for('y'..255) |c| {
        const str:[:0]const u8 = &[_:0]u8{@intCast(c)};
        try expect(!compiledDFA.isInLanguageCompiled(str));
    }
    for(1..255) |c1| {
        for(1..255) |c2| {
            const str:[:0]const u8 = &[_:0]u8{@intCast(c1), @intCast(c2)};
            try expect(!compiledDFA.isInLanguageCompiled(str));
        }
    }
}


test "nfas with ranges compiled" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var nfa = try RegExNFA.init(arena.allocator());
    try nfa.addStates(6);
    _ =try nfa.addRangeTransitionByState(0, .{'a', 'z'}, &[_]u32{1});
    _ =try nfa.addRangeTransitionByState(0, .{'A', 'Z'}, &[_]u32{1});
    _ =try nfa.addRangeTransitionByState(0, .{'b', 'z'}, &[_]u32{2});
    _ =try nfa.addRangeTransitionByState(0, .{'b', 'z'}, &[_]u32{2});

    // these are transitions to useless trap states (4, 5), just to throw the thing off
    _ =try nfa.addRangeTransitionByState(1, .{'0', '9'}, &[_]u32{4});
    _ =try nfa.addRangeTransitionByState(2, .{'0', '9'}, &[_]u32{5});

    _ =try nfa.addRangeTransitionByState(1, .{'5', '9'}, &[_]u32{3});
    _ =try nfa.addRangeTransitionByState(2, .{'0', '4'}, &[_]u32{3});
    _ =try nfa.designateStatesFinal(&[_]u32{3});

    try nfa.backUpEpsTransitions(); // technically unnecessary, but just to test it
    var dfa = try nfa.toPowersetConstructedDFA(.{});

    //const fa = FiniteAutomaton{.dfa = &dfa};
    //try fa.printDOT(std.io.getStdOut().writer());

    var compiled = try dfa.compile(&arena, false, .{});
    

    // tests
    for(1..'z') |c| {
        // holy shit is that an annoying way to initialize 'c', '\0' ...
        const str:[:0]const u8 = &[_:0]u8{@intCast(c)};
        try expect(!dfa.isInLanguageInterpreted(str));
        try expect(!compiled.isInLanguageCompiled(str));
    }

    for('a'..'z') |c1| {
        for('0'..'5') |c2| {
            const str:[:0]const u8 = &[_:0]u8{@intCast(c1), @intCast(c2)};
            if(c1 == 'a'){
                try expect(!dfa.isInLanguageInterpreted(str));
                try expect(!compiled.isInLanguageCompiled(str));
            }else{
                try expect(dfa.isInLanguageInterpreted(str));
                try expect(compiled.isInLanguageCompiled(str));
            }
        }
        for('5'..('9'+1)) |c2| {
            const str:[:0]const u8 = &[_:0]u8{@intCast(c1), @intCast(c2)};
            try expect(dfa.isInLanguageInterpreted(str));
            try expect(compiled.isInLanguageCompiled(str));
        }
    }

    for('A'..'Z') |c1| {
        for('0'..'5') |c2| {
            const str:[:0]const u8 = &[_:0]u8{@intCast(c1), @intCast(c2)};
            try expect(!dfa.isInLanguageInterpreted(str));
            try expect(!compiled.isInLanguageCompiled(str));
        }
        for('5'..('9'+1)) |c2| {
            const str:[:0]const u8 = &[_:0]u8{@intCast(c1), @intCast(c2)};
            try expect(dfa.isInLanguageInterpreted(str));
            try expect(compiled.isInLanguageCompiled(str));
        }
    }
}

test "regex dfa profiling" {
    const input = "xyz|w*(abc)*de*f";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);

    var dfa = try regex.toDFA(.{});

    var profileInfo = try RegExDFA.ProfilingInformation.init(std.testing.allocator, dfa.numStates);
    defer profileInfo.deinit();

    for(1..4) |runNumber| {
        try dfa.staticallyProfileOneRun("xyz", &profileInfo);
        try expect(runNumber == profileInfo.transitionFequencyPerState[dfa.startState].find('x').?);
        const stateOne = dfa.transitions[dfa.startState].find('x').?;
        try expect(runNumber == profileInfo.transitionFequencyPerState[stateOne].find('y').?);
        const stateTwo = dfa.transitions[stateOne].find('y').?;
        try expect(runNumber == profileInfo.transitionFequencyPerState[stateTwo].find('z').?);

        try expect(runNumber == profileInfo.visitsPerState[dfa.startState]);
        try expect(runNumber == profileInfo.visitsPerState[stateOne]);
        try expect(runNumber == profileInfo.visitsPerState[stateTwo]);
        // don't increment the final state, as that is not left
        try expect(0 == profileInfo.visitsPerState[dfa.transitions[stateTwo].find('z').?]);

        // these should be the only entries -> check that all are runNumber
        for(profileInfo.transitionFequencyPerState) |transitions| {
            for(transitions.map.items) |transition| {
                try expect(transition[1][1] == runNumber);
            }
        }
    }

    const compiled = try dfa.compile(&arena, true, .{.profileInfo = profileInfo});
    const startOfRecognize:[*]u8 = @ptrCast(compiled.recognize);
    // if the profiling has worked right, the first comparison should be comparing to x, i.e. the start of the recognize function should be:
    // sub rsp, 0x8
    // mov rax, rsi
    // mov cl, byte ptr [rax]
    // add rax, 0x1
    // cmp cl, 0x78; this compares to 'x'
    // -> check this
    try expect(std.mem.eql(u8, startOfRecognize[0..16], "\x48\x83\xEC\x08\x48\x89\xF0\x8A\x08\x48\x83\xC0\x01\x80\xF9\x78"));
}

test "regex range dfa profiling" {
    const input = "[a-x][by]z|w*(abc)*de*f";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const regex = try Parser.parseNoDiagnostic(arena.allocator(), input);

    var dfa = try regex.toDFA(.{});

    var profileInfo = try RegExDFA.ProfilingInformation.init(std.testing.allocator, dfa.numStates);
    defer profileInfo.deinit();

    for(1..4) |runNumber| {
        try dfa.staticallyProfileOneRun("xyz", &profileInfo);
        try expect(runNumber == profileInfo.transitionFequencyPerState[dfa.startState].find('x').?);
        const stateOne = dfa.transitions[dfa.startState].find('x').?;
        try expect(runNumber == profileInfo.transitionFequencyPerState[stateOne].find('y').?);
        const stateTwo = dfa.transitions[stateOne].find('y').?;
        try expect(runNumber == profileInfo.transitionFequencyPerState[stateTwo].find('z').?);

        try expect(runNumber == profileInfo.visitsPerState[dfa.startState]);
        try expect(runNumber == profileInfo.visitsPerState[stateOne]);
        try expect(runNumber == profileInfo.visitsPerState[stateTwo]);
        // don't increment the final state, as that is not left
        try expect(0 == profileInfo.visitsPerState[dfa.transitions[stateTwo].find('z').?]);

        // these should be the only entries -> check that all are runNumber
        for(profileInfo.transitionFequencyPerState) |transitions| {
            for(transitions.map.items) |transition| {
                try expect(transition[1][1] == runNumber);
            }
        }
    }

    const compiled = try dfa.compile(&arena, true, .{.profileInfo = profileInfo});
    const startOfRecognize:[*]u8 = @ptrCast(compiled.recognize);
    // if the profiling has worked right, the first comparison should be comparing to x, i.e. the start of the recognize function should be:
    // sub rsp, 0x8
    // mov rax, rsi
    // mov cl, byte ptr [rax]
    // add rax, 0x1
    // cmp cl, 0x78; this compares to 'x'
    // -> check this
    try expect(std.mem.eql(u8, startOfRecognize[0..16], "\x48\x83\xEC\x08\x48\x89\xF0\x8A\x08\x48\x83\xC0\x01\x80\xF9\x78"));
}

const fadec = @cImport({
    @cInclude("fadec.h");
    @cInclude("fadec-enc.h");
});

const FeMnem = u64;
const FeError = error{EncodeError};


// somehow they broke the nice struct initialization in zig 0.12..., need to manually force it to be a tuple type
fn ForceTuple(almostTupleType:type) type {
    const typeInfo = @typeInfo(almostTupleType);
    return @Type(.{
        .Struct = .{
            .is_tuple = true,
            .layout = .auto,
            .decls = &.{},
            .fields = typeInfo.Struct.fields,
        }
    });
}

fn encode(bufPtr:*[*]u8, mnem:FeMnem, args:ForceTuple(struct{@"0":fadec.FeOp = 0, @"1":fadec.FeOp = 0, @"2":fadec.FeOp = 0, @"3":fadec.FeOp = 0,})) FeError!void {
    const ret = fadec.fe_enc64_impl(@ptrCast(bufPtr), mnem, args[0], args[1], args[2], args[3]);
    if(ret != 0)
        return FeError.EncodeError;
}

test "fadec basic functionality and abstractions" {
    const buf:[]u8 = try cAllocer.alloc(u8, 256);
    var cur:[*]u8 = buf.ptr;
    const curPtr:[*c][*c]u8 = @ptrCast(&cur); // in zig-style this is not right, but the c translation of fadec expects this type, instead of the more sensible *[*]u8

    _ = fadec.fe_enc64_impl(curPtr, fadec.FE_ADD8rr, fadec.FE_AX, fadec.FE_AX, 0, 0);
    const length = @intFromPtr(cur) - @intFromPtr(buf.ptr);

    try encode(&cur, fadec.FE_ADD8rr, .{fadec.FE_AX, fadec.FE_AX});
    try expect(2*length == @intFromPtr(cur) - @intFromPtr(buf.ptr));

    try expect(std.mem.eql(u8, buf[0..length], buf[length..2*length]));
}

pub fn main() !void {
    //const writer = std.io.getStdOut().writer();
    //_ = writer;

    var arena = std.heap.ArenaAllocator.init(cAllocer);
    defer arena.deinit();

    //const input = "xyz|w*(abc)*de*f";
    //
    //var tok = try Tokenizer.init(arena.allocator(), input);
    //defer tok.deinit();
    //const regex = try Parser.init(arena.allocator(), &tok);
    //assert(!tok.hasNext(), "expected EOF, but there were tokens left", .{});
    //
    //var dfa = try regex.toDFA(.{});
    //
    //assert(dfa.internalAllocator.ptr == arena.allocator().ptr, "dfa should use the same allocator as the regex", .{});
    //
    ////var compiled = try dfa.compile(&arena, false, .{});
    ////debugLog("{}", .{compiled.isInLanguageCompiled("xyz")});
    ////compiled.debugPrint();
    //
    //const fa = FiniteAutomaton{.dfa = &dfa};
    //
    //try fa.printDOT(writer);


    //const fa = FiniteAutomaton{.dfa = &dfa};
    //try fa.printDOT(std.io.getStdOut().writer());


    const input = "[z-a]";
    //var tok = try Tokenizer.init(cAllocer, input);
    //defer tok.deinit();
    //const regex = try Parser.init(cAllocer, &tok);
    //try regex.printDOTRoot(writer);


    _ = compileInputString(&arena, input, .{}) catch {};


    //var fa = FiniteAutomaton{.dfa = &dfa};
    //try fa.printDOT(std.io.getStdOut().writer());
}
