#[macro_use]
pub mod lit;
pub mod cnf;
pub mod dimacs;

mod binary;
mod clause;
mod context;
mod load;
mod prop;
mod state;
mod tmp;

mod vec_mut_scan;
