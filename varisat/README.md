# Varisat

Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean
formula in [conjunctive normal form][cnf], it either finds a variable
assignment that makes the formula true or finds a proof that this is
impossible.

[cdcl]: https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning
[cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form

This is the library version. Varisat is also available as a command line solver
([`varisat-cli` on crates.io][crate-varisat-cli]).

## Documentation

  * [User Manual](https://jix.github.io/varisat/manual/0.2.1/)
  * [Library API Documentation](https://docs.rs/varisat/0.2.2/varisat/)

## Developer Documentation

The internal APIs are documented using rustdoc. It can be generated using
`cargo doc --document-private-items --all --exclude varisat-cli` or [viewed
online (master)][dev-docs].

You can also read [a series of blog posts about the development of
varisat][blog-series].

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
[dev-docs]: https://jix.github.io/varisat/dev/varisat/
[blog-series]: https://jix.one/tags/refactoring-varisat/
[crate-varisat]: https://crates.io/crates/varisat
[crate-varisat-cli]: https://crates.io/crates/varisat-cli
