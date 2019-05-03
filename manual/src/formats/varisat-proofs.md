# Varisat Proofs

Varisat has its own custom proof format. The format is not documented and may
change from version to version. Varisat comes with a built in checker for this
format ([command line][checker-cli] and [library][checker-lib]).

The format is inspired by the [LRAT] format but replaces clause ids by clause
hashes. This makes it simpler to generate and avoids any memory overhead during
proof generation. More details can be found in this [blog-post about Varisat
proofs][blog].

[checker-cli]: ../cli/proofs.md
[checker-lib]: ../lib/proofs.md
[LRAT]: ./lrat-proofs.md
[blog]: https://jix.one/refactoring-varisat-5-incremental-solving-and-proofs/
