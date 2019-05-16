//! Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean formula in
//! [conjunctive normal form][cnf], it either finds a variable assignment that makes the formula
//! true or finds a proof that this is impossible.
//!
//! In addition to this API documentation, Varisat comes with a [user manual].
//!
//! [cdcl]: https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning
//! [cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form
//! [user manual]: https://jix.github.io/varisat/manual/0.2.0/

#[macro_use]
pub mod checker;
pub mod config;
pub mod solver;

mod analyze_conflict;
mod binary;
mod cdcl;
mod clause;
mod context;
mod decision;
mod glue;
mod incremental;
mod load;
mod proof;
mod prop;
mod schedule;
mod simplify;
mod state;
mod tmp;

#[cfg(test)]
mod test;

pub use varisat_formula::{cnf, lit, CnfFormula, Lit, Var};

pub mod dimacs {
    //! DIMCAS CNF parser and writer.
    pub use varisat_dimacs::*;
}
