# Basic Solving

To solve a formula, we start with creating a SAT solver object.

```rust
# extern crate varisat;
use varisat::solver::Solver;

let mut solver = Solver::new();
```

## Loading a Formula

The solver also implements the `ExtendFormula` trait, so we already know how to
add clauses from the previous chapter.

```rust
# extern crate varisat;
# use varisat::Solver;
# let mut solver = Solver::new();
use varisat::ExtendFormula;

let (x, y, z) = solver.new_lits();

solver.add_clause(&[x, y, z]);
solver.add_clause(&[!x, !y]);
solver.add_clause(&[!y, !z]);
```

We can also load a `CnfFormula` with a single call of the `add_formula` method.

```rust
# extern crate varisat;
# use varisat::Solver;
# let mut solver = Solver::new();
# let (x, y, z) = solver.new_lits();
use varisat::{CnfFormula, ExtendFormula};
let mut formula = CnfFormula::new();
formula.add_clause(&[x, y, z]);
formula.add_clause(&[!x, !y]);
formula.add_clause(&[!y, !z]);

solver.add_formula(&formula);
```

If our formula is stored as [DIMACS CNF][dimacs] in a file, or in another way
that supports `std::io::Read`, we can load it into the solver with
`add_dimacs_cnf`. This uses incremental parsing, making it more efficient than
reading the whole formula into a `CnfFormula` first.

```rust
# extern crate varisat;
# use varisat::Solver;
# let mut solver = Solver::new();
let dimacs_cnf = b"1 2 3 0\n-1 -2 0\n-2 -3 0\n";

solver.add_dimacs_cnf(&dimacs_cnf[..]).expect("parse error");
```

## Finding a Solution

After loading a formula, we can ask the solver to find a solution:

```rust
# extern crate varisat;
# use varisat::Solver;
# let mut solver = Solver::new();
# let dimacs_cnf = b"1 2 3 0\n-1 -2 0\n-2 -3 0\n";
# solver.add_dimacs_cnf(&dimacs_cnf[..]).expect("parse error");
let solution = solver.solve().unwrap();

assert_eq!(solution, true); // satisfiable
```

While the solve method returns a `Result`, in the default configuration it
cannot fail. This means it is safe to unwrap the result here.

We might not only be interested in whether the formula is satisfiable, but also
want to know a satisfying assignment. With the `Solver::model` method, we can
query the solver for a set of assignments that make all clauses true.

```rust
# extern crate varisat;
# use varisat::{Solver, ExtendFormula};
# let mut solver = Solver::new();
# let (x, y, z) = solver.new_lits();
# let dimacs_cnf = b"1 2 3 0\n-1 -2 0\n-2 -3 0\n";
# solver.add_dimacs_cnf(&dimacs_cnf[..]).expect("parse error");
# let solution = solver.solve().unwrap();
let model = solver.model().unwrap(); // None if solve didn't return Ok(true)

assert!(model.contains(&x) || model.contains(&y) || model.contains(&z));
assert!(model.contains(&!x) || model.contains(&!y));
assert!(model.contains(&!y) || model.contains(&!z));
```


[dimacs]: (../formats/dimacs.md)
