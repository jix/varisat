# Basic Usage

The command line solver reads and solves a single formula. The file name of the
formula to solve is passed as an argument on the command line. If no file is
specified, Varisat will read a formula from the standard input. The formula is
parsed as a [DIMACS CNF] file.

During the solving process, Varisat will print some statistics on lines
starting with `c `. In general it is not possible to infer the solving process
from these statistics and it is not necessary to understand them to use a SAT
solver. They are intended for the expert user and solver developers who are
familiar with the solver's internals.

Solving an instance can take from milliseconds to forever and anything in
between. There is no known algorithm that will efficiently solve all possible
SAT formulas. Nevertheless the algorithms and heuristics used by SAT solvers
are often successful. Most of the time it's not possible to tell whether they
are effective for a given formula.

If Varisat is able to find a satisfying assignment or is able to determine that
there is no such assignment, it will print a solution line. This is either `s
SATISFIABLE` or `s UNSATISFIABLE` depending on the verdict.

If there is a satisfying assignment it will be output on lines starting with `v
`, followed by a list of literals. Assigning these literals to true will make
the input formula true.

The exit code of the solver will also indicate the solver's verdict. When the
formula is satisfiable, the exit code `10` will be returned. When it is
unsatisfiable the exit code will be `20`.

In the next chapter we will see how to generate a proof of unsatisfiability in
case no satisfying assignment exists.

## Satisfiable Example

This shows an example run for the satisfiable formula
[sgen1_sat_90_0.cnf](../examples/sgen1_sat_90_0.cnf):

```txt
$ varisat sgen1_sat_90_0.cnf
c This is varisat [...]
c   release build - rustc [...]
c Reading file 'sgen1_sat_90_0.cnf'
c Parsed formula with 90 variables and 216 clauses
c [...]
s SATISFIABLE
v 1 -2 -3 -4 -5 -6 -7 8 -9 -10 11 -12 -13 -14 -15 -16 17 -18 -19 -20 -21 22 -23 -24 -25 -26 -27 -28 29 -30 -31 32 -33 -34 -35 -36 -37 -38 -39 40 -41 -42 43 -44 -45 46 -47 -48 -49 -50 -51 52 -53 -54 -55 -56 -57 -58 -59 60 -61 62 -63 -64 -65 -66 -67 68 -69 -70 -71 -72 -73 -74 75 -76 -77 78 -79 -80 -81 -82 -83 84 -85 -86 -87 -88 89 -90 0
```

## Unsatisfiable Example

This shows an example run for the unsatisfiable formula
[sgen1_unsat_57_0.cnf](../examples/sgen1_unsat_57_0.cnf):

```txt
$ varisat sgen1_unsat_57_0.cnf
c This is varisat [...]
c   release build - rustc [...]
c Reading file 'sgen1_unsat_57_0.cnf'
c Parsed formula with 57 variables and 124 clauses
c [...]
s UNSATISFIABLE
```

[DIMACS CNF]: ../common/dimacs.md
