# Varisat

Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean
formula in [conjunctive normal form][cnf], it either finds a variable
assignment that makes the formula true or finds a proof that this is
impossible.

Varisat is open source software. You can find the Varisat project on [GitHub].

Varisat is available as a rust library ([`varisat` on
crates.io][crate-varisat]) and as a command line solver ([`varisat-cli` on
crates.io][crate-varisat-cli]).

In addition to this user manual, Varisat comes with an [API
documentation][api-docs].


[cdcl]: https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning
[cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form
[crate-varisat]: https://crates.io/crates/varisat
[crate-varisat-cli]: https://crates.io/crates/varisat-cli
[github]: https://github.com/jix/varisat
[api-docs]: https://docs.rs/crate/varisat
