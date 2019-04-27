//! Varisat is a [CDCL][cdcl] based SAT solver written in rust. Given a boolean formula in
//! [conjunctive normal form][cnf], it either finds a variable assignment that makes the formula true or
//! finds a proof that this is impossible.
//!
//! [cdcl]: https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning
//! [cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form

#[macro_use]
pub mod lit;
pub mod checker;
pub mod cnf;
pub mod dimacs;
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

mod vec_mut_scan;

#[cfg(test)]
mod test;
