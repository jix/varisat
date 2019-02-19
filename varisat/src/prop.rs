//! Unit propagation.
pub mod assignment;
pub mod graph;
pub mod watch;

pub use assignment::{enqueue_assignment, Assignment, Trail};
pub use graph::{Conflict, ImplGraph, ImplNode, Reason};
pub use watch::{Watch, Watchlists};
