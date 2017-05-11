# flat-checker

## Installation

```
git clone git@github.com:apirogov/flat-checker.git
cd flat-checker
stack install
```

## Usage

The program needs at least an input graph, a formula and a schema size:

`flat-checker -g FILE -f FORMULA -n SIZE`

The file must describe a directed graph with labeled nodes in DOT format (from
GraphViz) as shown in the `examples/` directory. If no file argument is
provided, the graph is read from standard input.

The LTL formula has the following grammar:

```
  φ ::= true | false | p | ~φ | (φ) | (φ & φ) | (φ | φ) | Xφ | F[C]φ | G[C]φ | (φ U[C] φ)
  C ::= <int> φ <+/-> ... <+/-> <int> φ <Op> <int>
  Op ::= > | >= | = | <= | <
```

`p` is an atomic proposition represented by a string starting with a lowercase letter.
Whitespace is ignored, the parentheses around binary operators are mandatory.
The `[C]` is an optional constraint over a linear combination of formulae, with the
meaning that occurences of these formulae are counted and weighted by the given
coefficients within the scope described by the `U`. An `φU[C]ψ` is then only fulfilled,
if the constraint is satisfied at the `ψ`-position.

A larger path schema size makes the resulting formula larger and the calculation
slower, but may be necessary to find a run that satisfies the given formula.

See `flat-checker -h` for a complete list of possible command line arguments.
