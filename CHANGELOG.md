# 0.2.2 (2020-09-09)

  * Upgrade dependencies
  * Replace unmaintained `failure` library with `anyhow` and `thiserror`
  * Address all clippy warnings

# 0.2.1 (2019-05-18)

  * Improved API for constructing formulas (#54 and #55)
  * Fix proof generation when the formula contains duplicated unit clauses
    (#26)
  * Configurable search parameters (#39)
  * Proofs for satisfiable instances (#47)
  * Proofs for incremental solving (#48)
  * Reduce size of proofs in native format (#42)
  * Split independent parts into individual crates with re-exports (#51)

# 0.2.0 (2019-05-04)

Initial release
