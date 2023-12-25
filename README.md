# zig-re
RegEx in Zig. Not much more to it than that.

At the moment, only parsing is implemented, with a Graphviz DOT output format.

Example of a regex combining all current features: `xyz|w*(abc)*de*f`
AST:

![](assets/example.svg)
