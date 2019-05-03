# Basic Solving

To solve a formula, we start with creating a SAT solver object.

```rust
# extern crate varisat;
use varisat::solver::Solver;

let mut solver = Solver::new();
```

## Loading a Formula

We can load a formula by adding individual clauses:

```rust
# extern crate varisat;
# use varisat::solver::Solver;
# let mut solver = Solver::new();
use varisat::lit::Lit;

let (x, y, z) = (Lit::from_dimacs(1), Lit::from_dimacs(2), Lit::from_dimacs(3));

solver.add_clause(&[x, y, z]);
solver.add_clause(&[!x, !y]);
solver.add_clause(&[!y, !z]);
```

By adding a formula:

```rust
# extern crate varisat;
# use varisat::solver::Solver;
# use varisat::lit::Lit;
# let mut solver = Solver::new();
# let (x, y, z) = (Lit::from_dimacs(1), Lit::from_dimacs(2), Lit::from_dimacs(3));
use varisat::cnf::CnfFormula;
let mut formula = CnfFormula::new();
formula.add_clause(&[x, y, z]);
formula.add_clause(&[!x, !y]);
formula.add_clause(&[!y, !z]);

solver.add_formula(&formula);
```

Or by directly loading a [DIMACS CNF][dimacs] from anything that implements
`std::io::Read`. This uses incremental parsing, making it more efficient than
reading the whole formula into a `CnfFormula`.

```rust
# extern crate varisat;
# use varisat::solver::Solver;
# let mut solver = Solver::new();
let dimacs_cnf = b"1 2 3 0\n-1 -2 0\n-2 -3 0\n";

solver.add_dimacs_cnf(&dimacs_cnf[..]).expect("parse error");
```

## Finding a Solution

After loading a formula, we can ask the solver to find a solution:

```rust
# extern crate varisat;
# use varisat::solver::Solver;
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
# use varisat::solver::Solver;
# use varisat::lit::Lit;
# let mut solver = Solver::new();
# let (x, y, z) = (Lit::from_dimacs(1), Lit::from_dimacs(2), Lit::from_dimacs(3));
# let dimacs_cnf = b"1 2 3 0\n-1 -2 0\n-2 -3 0\n";
# solver.add_dimacs_cnf(&dimacs_cnf[..]).expect("parse error");
# let solution = solver.solve().unwrap();
let model = solver.model().unwrap(); // None if solve didn't return Ok(true)

assert!(model.contains(&x) || model.contains(&y) || model.contains(&z));
assert!(model.contains(&!x) || model.contains(&!y));
assert!(model.contains(&!y) || model.contains(&!z));
```


[dimacs]: (../formats/dimacs.md)
