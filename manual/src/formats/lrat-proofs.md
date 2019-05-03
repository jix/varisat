# LRAT Proofs

LRAT is a proof format that extends DRAT with additional information to
simplify the checking of clause additions. This makes it possible to write
efficient formally verified proof checkers.

LRAT is described in the paper ["Efficient Certified RAT Verification"][LRAT]
by Cruz-Filipe, Heule, Hunt, Kaufmann and Schneider-Kamp. The authors suggested
generating LRAT proofs from [DRAT] proofs. Such a conversion requires checking
the DRAT proof which is often very time consuming.

Varisat allows generating LRAT proofs starting from its [own proof
format][varisat]. As Varisat's proof format is based on LRAT with modifications
that allow simpler and faster proof generation, such a conversion is much
faster. For the same solver and parameters, this results in a significant
reduction in the overall time required for a formally verified unsatisfiability
proof.

LRAT also has a more compact binary variant called CLRAT, both are supported by
Varisat.

The [ACL2 programming language and theorem prover][ACL2] distribution comes
with an efficient formally verified CLRAT proof checker. It can be found in the
subdirectory `books/projects/sat/lrat/incremental`.

[LRAT]: http://www.cs.utexas.edu/users/marijn/publications/lrat.pdf
[DRAT]: ./drat-proofs.md
[varisat]: ./varisat-proofs.md
[ACL2]: http://www.cs.utexas.edu/users/moore/acl2/
