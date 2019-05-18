# Incremental Solving

Incremental solving means changing and re-solving a formula multiple times,
without starting the search from scratch. This can save a lot of time, when
many related formulas that differ only slightly have to be solved.

Varisat supports two features that enable incremental solving. These are
incremental clause additions and solving under assumptions.

## Incremental Clause Additions

Incremental clause additions simply means that further calls to
`Solver::add_clause`, `Solver::add_formula` or `Solver::add_dimacs_cnf` are
allowed after `Solver::solve` returned. The new clauses are added to the
clauses that were already present prior to the last `solve` call.

```rust
# extern crate varisat;
use varisat::{ExtendFormula, Solver};

let mut solver = Solver::new();

let (x, y, z) = solver.new_lits();

solver.add_clause(&[!x, y]);
solver.add_clause(&[!y, z]);
assert_eq!(solver.solve().unwrap(), true);

solver.add_clause(&[!z, x]);
assert_eq!(solver.solve().unwrap(), true);

solver.add_clause(&[!z, !y]);
solver.add_clause(&[z, y]);
assert_eq!(solver.solve().unwrap(), false);
```

### Solving Under Assumptions

Once clauses are added to the solver they cannot be removed anymore. Instead
assumptions can be used to limit the search to a subset of solutions.
Assumptions fix the values of certain variables. This is equivalent to adding
some unit clauses to the formula, with the difference that assumptions can be
removed again.

Assumptions are set by calling `Solver::assume`, which replaces any previous
assumptions.

Using additional helper variables, assumptions can be used to emulate removable
clauses:

```rust
# extern crate varisat;
use varisat::{ExtendFormula, Solver};

let mut solver = Solver::new();

let (x, y, z) = solver.new_lits();
let ignore_clauses = solver.new_lit();

solver.add_clause(&[!x, y]);
solver.add_clause(&[!y, z]);
assert_eq!(solver.solve().unwrap(), true);

solver.add_clause(&[!z, x]);
assert_eq!(solver.solve().unwrap(), true);

solver.add_clause(&[ignore_clauses, !z, !y]);
solver.add_clause(&[ignore_clauses, z, y]);

solver.assume(&[!ignore_clauses]);
assert_eq!(solver.solve().unwrap(), false);

solver.assume(&[]); // Clears assumptions
solver.add_clause(&[ignore_clauses]);

assert_eq!(solver.solve().unwrap(), true);
```

When a formula is unsatisfiable under multiple assumptions, Varisat may be able
to find a smaller set of assumptions that is sufficient for unsatisfiability.
Such a sufficient subset of assumptions can be retrieved using
`Solver::failed_core`.
