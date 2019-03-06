#[macro_use]
pub mod lit;
pub mod cnf;
pub mod dimacs;
pub mod solver;

mod analyze_conflict;
mod binary;
mod cdcl;
mod clause;
mod context;
mod decision;
mod load;
mod prop;
mod state;
mod tmp;

mod vec_mut_scan;

#[cfg(test)]
mod test;
