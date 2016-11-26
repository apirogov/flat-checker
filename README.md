# fltl-checker

## Installation

```
git clone git@github.com:apirogov/fltl-checker.git
cd fltl-checker
stack install
```

## Usage

`fltl-checker -g FILE -f FORMULA -n SIZE`

The file must describe a directed graph with labeled nodes in a simple format as
shown in the `examples/` directory or in DOT format (from GraphViz).
If no file argument is provided, the graph is read from standard input.

The LTL formula has the following grammar:

```
  φ ::= 1 | 0 | p | ~φ | (φ & φ) | (φ | φ) | Xφ | Fφ | Gφ | (φ U φ) | (φ U[m/n] φ)
```

`p` stands for an arbitrary lowercase letter representing a proposition, `1` means
**true**, `0` means **false**. Whitespace is ignored, additional parentheses are not allowed (yet),
while the parentheses around binary operators are mandatory. `m/n` can represent
  any fraction of natural numbers with `0 < m/n <= 1`.

A larger path schema size makes the resulting formula larger and the calculation
slower, but may be necessary to find a run that satisfies the given formula.
