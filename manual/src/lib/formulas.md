# Formulas

SAT solvers operate on formulas in [conjunctive normal form][cnf] (CNF). The
Varisat library comes with types to efficiently store CNF formulas. This is
independent from loading a formula into the solver. This is useful for writing
custom code that processes CNF formulas. It also simplifies writing code that
generates a formula to either directly solve it or alternatively write it to a
file.

## Literals and Variables

To build formulas in conjunctive normal form, we need to start with variables
and literals. For this Varisat provides the types `Var` and `Lit`.

A variable is identified by an integer. The convention used for
input and output of variables follows the [DIMACS CNF][dimacs]
format and is 1-based. A literal is a variable or a negated variable. In the
DIMACS format negative literals are represented by negative integers.

Internally variables are numbered starting with zero. This matches the array
indexing convention used by Rust. The 0-based number of a variable is called
index, while the 1-based number is called dimacs. Literals are also represented
by a non-negative number called the code. A literal's code is the corresponding
variable's index shifted to the left by one. The least significant bit is set
if the literal is negative.

The `Var` and `Lit` types come with methods to convert between the
representations. Note that `Lit::index` returns the corresponding variable's
index, not the literal's code.

```rust
# extern crate varisat;
use varisat::lit::{Var, Lit};

let x = Var::from_index(0);

assert_eq!(x, Var::from_dimacs(1));
assert_eq!(x.index(), 0);
assert_eq!(x.to_dimacs(), 1);

assert!(Lit::from_dimacs(2).is_positive());
assert!(Lit::from_dimacs(-3).is_negative());

assert_eq!(Lit::positive(x), Lit::from_var(x, false));
assert_eq!(Lit::negative(x), Lit::from_var(x, true));

assert_eq!(Lit::negative(x), !Lit::positive(x));

assert_eq!(Lit::from_index(6, false).code(), 12);
assert_eq!(Lit::from_index(6, true).code(), 13);

assert_eq!(Lit::from_code(13).var(), Var::from_dimacs(7));
assert_eq!(Lit::from_code(13).index(), 6);
```

When formatting variables or literals the DIMACS convention is used.

```rust
# extern crate varisat;
# use varisat::lit::{Var, Lit};

let fmt_display = format!("{}, {}", Var::from_dimacs(5), Lit::from_dimacs(-1));
let fmt_debug = format!("{:?}, {:?}", Var::from_dimacs(5), Lit::from_dimacs(-1));

assert_eq!(fmt_display, "5, -1");
assert_eq!(fmt_debug, "5, -1");
```

## Formulas

A CNF formula is a conjunction of clauses and a clause a disjunction of
literals. This means we can represent a formula as a set of sets of literals.

By arbitrarily ordering the elements of the sets, we could use a
`Vec<Vec<Lit>>` to represent a formula. Such a representation has too much
memory overhead per clause though. Each clause requires a separate allocation,
which also hurts cache locality when iterating over the clauses of a large
formula.

Instead Varisat provides the `CnfFormula` type, which stores all literals in a
single `Vec`. When iterating over a `CnfFormula` the clauses can be accessed as
slices.

```rust
# extern crate varisat;
# use varisat::lit::{Var, Lit};
use varisat::cnf::CnfFormula;

let mut formula = CnfFormula::new();

let (a, b, c) = (Lit::from_dimacs(1), Lit::from_dimacs(2), Lit::from_dimacs(3));

formula.add_clause(&[a, b, c]);
formula.add_clause(&[!a, !b]);
formula.add_clause(&[!b, !c]);
formula.add_clause(&[!a, !c]);

assert_eq!(formula.iter().last().unwrap(), &[!a, !c]);
```

## Parsing and Writing Formulas

Varisat provides routines for parsing and writing Formulas in the [DIMACS
CNF][dimacs] format.

```rust
# extern crate varisat;
# use varisat::lit::{Var, Lit};
use varisat::dimacs::{DimacsParser, write_dimacs};

let input = b"p cnf 3 2\n1 2 3 0\n-1 -3 0\n";

let implements_read = &input[..];

let mut formula = DimacsParser::parse(implements_read).expect("parse error");

formula.add_clause(&[Lit::from_dimacs(2)]);

let mut implements_write = vec![];

write_dimacs(&mut implements_write, &formula);

assert_eq!(implements_write, b"p cnf 3 3\n1 2 3 0\n-1 -3 0\n2 0\n");
```

[cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form
[dimacs]: (../formats/dimacs.md)
