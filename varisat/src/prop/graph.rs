//! The implication graph.

use partial_ref::{partial, PartialRef};

use crate::clause::ClauseRef;
use crate::context::{ClauseAllocP, Context};
use crate::lit::{Lit, LitIdx, Var};

/// Assignments that caused a propagation.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Reason {
    Unit,
    Binary([Lit; 1]),
    Long(ClauseRef),
}

impl Reason {
    /// The literals that caused the propagation.
    pub fn lits<'out, 'a, 'b>(&'a self, ctx: &'b partial!('b Context, ClauseAllocP)) -> &'out [Lit]
    where
        'a: 'out,
        'b: 'out,
    {
        match self {
            Reason::Unit => &[],
            Reason::Binary(lit) => lit,
            // The propagated literal is always kept at position 0
            Reason::Long(cref) => &ctx.part(ClauseAllocP).clause(*cref).lits()[1..],
        }
    }
}

/// Propagation that resulted in a conflict.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Conflict {
    Binary([Lit; 2]),
    Long(ClauseRef),
}

impl Conflict {
    /// The literals that caused the conflict.
    pub fn lits<'out, 'a, 'b>(&'a self, ctx: &'b partial!('b Context, ClauseAllocP)) -> &'out [Lit]
    where
        'a: 'out,
        'b: 'out,
    {
        match self {
            Conflict::Binary(lits) => lits,
            Conflict::Long(cref) => ctx.part(ClauseAllocP).clause(*cref).lits(),
        }
    }
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

    /// Get the reason for an assigned variable.
    ///
    /// Returns stale data if the variable isn't assigned.
    pub fn reason(&self, var: Var) -> &Reason {
        &self.nodes[var.index()].reason
    }

    /// Get the decision level of an assigned variable.
    ///
    /// Returns stale data if the variable isn't assigned.
    pub fn level(&self, var: Var) -> usize {
        self.nodes[var.index()].level as usize
    }

    /// Updates the reason for an assigned variable.
    ///
    /// Make sure the reason vars are in front of the assigned variable in the trail.
    pub fn update_reason(&mut self, var: Var, reason: Reason) {
        self.nodes[var.index()].reason = reason
    }
}
