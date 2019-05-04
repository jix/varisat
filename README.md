# Varisat

[![crates.io](https://img.shields.io/crates/v/varisat.svg)](https://crates.io/crates/varisat)
[![docs.rs](https://docs.rs/varisat/badge.svg)](https://docs.rs/varisat)
[![CircleCI branch](https://img.shields.io/circleci/project/github/jix/varisat/master.svg)](https://circleci.com/gh/jix/varisat/tree/master)
[![codecov](https://img.shields.io/codecov/c/gh/jix/varisat/master.svg)](https://codecov.io/gh/jix/varisat)
[![Developer Documentation](https://img.shields.io/badge/dev%20docs-master-blue.svg)](https://jix.github.io/varisat/dev/varisat/)
![](https://img.shields.io/crates/l/varisat.svg)

Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean
formula in [conjunctive normal form][cnf], it either finds a variable
assignment that makes the formula true or finds a proof that this is
impossible.

Varisat is available as a rust library ([`varisat` on
crates.io][crate-varisat]) and as a command line solver ([`varisat-cli` on
crates.io][crate-varisat-cli]).

## Installation

Varisat is available using rust's package manager cargo. The command line
solver can be installed or updated using `cargo install --force varisat-cli`.
Cargo can be installed using [rustup](https://rustup.rs/).

The command line solver is also available as a [pre-compiled binary][releases]
for Linux and Windows.

## Documentation

  * [User Manual](https://jix.github.io/varisat/manual/0.2.0/)
  * [Library API Documentation](https://docs.rs/crate/varisat)

## Developer Documentation

The internal APIs are documented using rustdoc. It can be generated using
`cargo doc --document-private-items --all --exclude varisat-cli` or [viewed
online (master)][dev-docs].

A version of the [user manual built from the master branch][manual-master] is
also available.

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
[manual-master]: https://jix.github.io/varisat/manual/master/
[releases]: https://github.com/jix/varisat/releases
