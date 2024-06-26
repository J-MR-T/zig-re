# zig-re
RegEx in Zig.

At the moment, parsing of basic RegEx's (literal characters, concatenation, `|`, and `*`) is implemented; `\` is used as an escaping character; parentheses can be used as you would expect. The empty string is not a valid regular expression - to match only the empty string, use the regex `[]`.  All other current features are merely syntactic sugar (as the previous features are enough to recognize any Type-3 language); here's a list of all the sweet stuff:
- Character ranges and groups: `[a-d]`, `[abcd]`, `[ab-d]`, `(a|b|c|d)` are all supported (and equivalent). Empty character ranges (i.e. `[]`) are the only case where ranges are not syntactic sugar, as there is no other way to regocnize only the empty string.
    - Character groups can be inverted: `[^a]` matches any character but `a`.
- Using `.` to mean "any character" is supported. To match a literal '.', use `[.]` or `\.`.
- The `+` operator can be used as a shorthand for a concatentation and a Kleene star: `x+` is equivalent to `xx*`, i.e. `+` means "at least one character".
- The `?` operator can be used as a shorthand for a union with the empty string: `x?` is equivalent to `x|[]`.


Translation of regular expressions to $\varepsilon$-NFA to NFA to DFA is implemented and seems to work in relatively complex scenarios. Canonicalization of the final DFA is not implemented yet, and $\varepsilon$-NFA to NFA conversion is not very efficient yet.

The RegEx ASTs, and the NFAs and DFAs include Graphviz DOT output as a visualization aid.

The project also includes a JIT compiler for x86-64 that can convert DFAs to machine code that is executable immediately. Profile guided optimization is also implemented: the JIT compiler can use information collected during profiling runs of the DFA (pre-compilation, i.e. interpreted runs), to emit more efficient machine code. Although the compile-time performance of using this feature is not great yet.

## Example
<!-- TODO incorporate escaping, +, ?, [], [^] -->
Example of a regex combining almost all current features: `x[yz]|.w*[a-c]*[f-i]`

AST:

![](assets/exampleAST.svg)

$\varepsilon$-NFA:

![](assets/exampleEpsNFA.svg)

NFA (still has the epsilon transitions, but they can all be ignored):

![](assets/exampleNFA.svg)

DFA:

![](assets/exampleDFA.svg)

Machine code can be found [here](assets/exampleMC.s)

## `comptime` ?
Building the DFA at compile-time should be possible quite easily [if/when Zig gets working compile-time allocators](https://github.com/ziglang/zig/issues/1291). It should also be possible now, but not without significant rewrites.
