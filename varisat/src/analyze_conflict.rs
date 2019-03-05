//! Learns a new clause by analyzing a conflict.
use std::mem::swap;

use partial_ref::{partial, split_borrow, PartialRef};

use crate::context::{AnalyzeConflictP, ClauseAllocP, Context, ImplGraphP, TrailP};
use crate::lit::{Lit, Var};
use crate::prop::Conflict;

/// Temporaries for conflict analysis
#[derive(Default)]
pub struct AnalyzeConflict {
    /// This is the learned clause after analysis finishes.
    clause: Vec<Lit>,
    /// Number of literals in the current clause at the current level.
    current_level_count: usize,
    /// Variables in the current clause.
    var_flags: Vec<bool>,
    /// Entries to clean in `var_flags`.
    to_clean: Vec<Var>,
}

impl AnalyzeConflict {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        self.var_flags.resize(count, false);
    }

    /// The learned clause.
    pub fn clause(&self) -> &[Lit] {
        &self.clause
    }
}

/// Learns a new clause by analyzing a conflict.
///
/// Returns the lowest decision level that makes the learned clause asserting.
pub fn analyze_conflict(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        ClauseAllocP,
        ImplGraphP,
        TrailP,
    ),
    conflict: Conflict,
) -> usize {
    split_borrow!(lit_ctx = &(ClauseAllocP) ctx);

    let analyze = ctx.part_mut(AnalyzeConflictP);

    analyze.clause.clear();
    analyze.current_level_count = 0;

    if ctx.part(TrailP).current_level() == 0 {
        // Conflict with no decisions, generate empty clause
        return 0;
    }

    drop(analyze);

    // We start with all the literals of the conflicted clause
    for &lit in conflict.lits(lit_ctx.borrow()) {
        add_literal(ctx.borrow(), lit);
    }

    // TODO update clause stats

    // To get rid of all but one literal of the current level, we resolve the clause with the reason
    // for those literals. The correct order for this is reverse chronological.

    for &lit in ctx.part(TrailP).trail().iter().rev() {
        let analyze = ctx.part_mut(AnalyzeConflictP);
        let lit_present = &mut analyze.var_flags[lit.index()];
        // Is the lit present in the current clause?
        if *lit_present {
            *lit_present = false;
            analyze.current_level_count -= 1;
            if analyze.current_level_count == 0 {
                // lit is the last literal of the current level present in the current clause,
                // therefore the resulting clause will assert !lit so we put in position 0
                analyze.clause.push(!lit);
                let end = analyze.clause.len() - 1;
                analyze.clause.swap(0, end);

                break;
            } else {
                // We removed the literal and now add its reason.
                let reason = ctx.part(ImplGraphP).reason(lit.var());

                for &lit in reason.lits(lit_ctx.borrow()) {
                    add_literal(ctx.borrow(), lit);
                }

                // TODO update clause stats
            }
        }
    }

    let analyze = ctx.part_mut(AnalyzeConflictP);

    for var in analyze.to_clean.drain(..) {
        analyze.var_flags[var.index()] = false;
    }

    // TODO minimize clause

    // We find the highest level literal besides the asserted literal and move it into position 1.
    // This is important to ensure the watchlist constraints are not violated on backtracking.
    let mut backtrack_to = 0;

    if analyze.clause.len() > 1 {
        let (prefix, rest) = analyze.clause.split_at_mut(2);
        let lit_1 = &mut prefix[1];
        backtrack_to = ctx.part(ImplGraphP).level(lit_1.var());
        for lit in rest.iter_mut() {
            let lit_level = ctx.part(ImplGraphP).level(lit.var());
            if lit_level > backtrack_to {
                backtrack_to = lit_level;
                swap(lit_1, lit);
            }
        }
    }

    backtrack_to
}

/// Add a literal to the current clause.
fn add_literal(mut ctx: partial!(Context, mut AnalyzeConflictP, ImplGraphP, TrailP), lit: Lit) {
    let (analyze, mut ctx) = ctx.split_part_mut(AnalyzeConflictP);
    let lit_level = ctx.part(ImplGraphP).level(lit.var());
    // No need to add literals that are set by unit clauses or already present
    if lit_level > 0 && !analyze.var_flags[lit.index()] {
        // TODO update var stats
        analyze.var_flags[lit.index()] = true;
        if lit_level == ctx.part(TrailP).current_level() {
            analyze.current_level_count += 1;
        } else {
            analyze.clause.push(lit);
            analyze.to_clean.push(lit.var());
        }
    }
}
