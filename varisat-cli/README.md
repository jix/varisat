# Varisat

Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean
formula in [conjunctive normal form][cnf], it either finds a variable
assignment that makes the formula true or finds a proof that this is
impossible.

This is the command line version. Varisat is also available as a library
([`varisat` on crates.io][crate-varisat]).

## License

The Varisat source code is licensed under either of

  * Apache License, Version 2.0
    ([LICENSE-APACHE](LICENSE-APACHE) or
    http://www.apache.org/licenses/LICENSE-2.0)
  * MIT license
    ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in Varisat by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[cdcl]: https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning
[cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form
[crate-varisat]: https://crates.io/crates/varisat
[crate-varisat-cli]: https://crates.io/crates/varisat-cli
