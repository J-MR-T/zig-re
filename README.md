# zig-re
RegEx in Zig.

At the moment, parsing of basic RegEx's (literal characters, concatenation, `|`, and `*`) is implemented, with a Graphviz DOT output format.

Translation of regular expressions to $\varepsilon$-NFA to NFA to DFA is implemented and seems to work in somewhat complex scenarios, but is not tested extensively yet. Canonicalization of the final DFA is not implemented yet, and $\varepsilon$-NFA to NFA conversion is not very efficient yet.

Example of a regex combining all current features: `xyz|w*(abc)*de*f`

AST:

![](assets/exampleAST.svg)

$\varepsilon$-NFA:

![](assets/exampleEpsNFA.svg)

NFA (still has the epsilon transitions, but they can all be ignored):

![](assets/exampleNFA.svg)

DFA:

![](assets/exampleDFA.svg)

## `comptime` ?
Building the DFA at compile-time should be possible quite easily (if/when Zig gets working compile-time allocators)[https://github.com/ziglang/zig/issues/1291]. It should also be possible now, but not without significant rewrites.
