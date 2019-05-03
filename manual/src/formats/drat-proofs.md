# DRAT Proofs

DRAT is the de-facto standard format for unsatisfiability proofs. It is required for solvers taking part in the yearly SAT competition. It is a minimal clausal proof format, that lists additions and removals of clauses. It does not contain any justification for clause additions. This makes DRAT proofs easy and efficient to generate, comparatively compact, but involves more work during checking.

DRAT has an ASCII and a binary encoding, both are supported by Varisat.

More information about it as well as proof checker can be found on the
[DRAT-trim] page.

[DRAT-trim]: https://github.com/marijnheule/drat-trim
