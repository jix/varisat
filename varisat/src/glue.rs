//! Compute glue levels of clauses.
//!
//! The glue level of a propagating clause is the number of distinct decision levels of the clause's
//! variables. This is also called the literal block distance (LBD). For each clause the smallest
//! glue level observed is used as an indicator of how useful that clause is.

use partial_ref::{partial, PartialRef};

use varisat_formula::Lit;

use crate::context::{parts::*, Context};

/// Compute the glue level of a clause.
pub fn compute_glue(mut ctx: partial!(Context, mut TmpDataP, ImplGraphP), lits: &[Lit]) -> usize {
    let (tmp_data, ctx) = ctx.split_part_mut(TmpDataP);
    let impl_graph = ctx.part(ImplGraphP);
    let flags = &mut tmp_data.flags;

    let mut glue = 0;

    for &lit in lits {
        let level = impl_graph.level(lit.var());
        let flag = &mut flags[level];
        if !*flag {
            *flag = true;
            glue += 1
        }
    }

    for &lit in lits {
        let level = impl_graph.level(lit.var());
        flags[level] = false;
    }

    glue
}
