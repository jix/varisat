# Varisat

[![Build Status](https://api.cirrus-ci.com/github/jix/varisat.svg)](https://cirrus-ci.com/github/jix/varisat)
[![codecov](https://codecov.io/gh/jix/varisat/branch/master/graph/badge.svg)](https://codecov.io/gh/jix/varisat)
[![Developer Documentation](https://img.shields.io/badge/dev%20docs-master-blue.svg)](https://jix.github.io/varisat/varisat/)
![](https://img.shields.io/crates/l/varisat.svg)

Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean
formula in conjunctive normal form, it either finds a variable assignment that
makes the formula true or finds a proof that this is impossible.

This repository is for varisat 0.2, a rewrite of varisat 0.1. This is not in a
usable state yet.

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
[dev-docs]: https://jix.github.io/varisat/varisat/
[blog-series]: https://jix.one/tags/refactoring-varisat/
