//! The implication graph.
use crate::clause::ClauseRef;
use crate::lit::{Lit, LitIdx};

/// Assignments that caused a propagation.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Reason {
    Unit,
    Binary([Lit; 1]),
    Long(ClauseRef),
}

/// Propagation that resulted in a conflict.
pub enum Conflict {
    Unit([Lit; 1]),
    Binary([Lit; 2]),
    Long(ClauseRef),
}

/// Node and incoming edges of the implication graph.
#[derive(Copy, Clone)]
pub struct ImplNode {
    pub reason: Reason,
    pub level: LitIdx,
}

/// The implication graph.
///
/// This is a DAG having all assigned variables as nodes. It has unit clauses, assumptions and
/// decisions as sources. For each propagated assignment it has incomming edges from the literals
/// whose assignment caused the propagation to happen.
#[derive(Default)]
pub struct ImplGraph {
    /// Contains only valid data for indices of assigned variables.
    pub nodes: Vec<ImplNode>,
}

impl ImplGraph {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        self.nodes.resize(
            count,
            ImplNode {
                reason: Reason::Unit,
                level: 0,
            },
        );
    }
}
