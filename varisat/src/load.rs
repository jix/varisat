//! Loading a formula into the solver.
use partial_ref::{partial, PartialRef};

use crate::clause::{db, ClauseHeader, Tier};
use crate::context::{
    AssignmentP, BinaryClausesP, ClauseAllocP, ClauseDbP, Context, ImplGraphP, IncrementalP,
    ProofP, SolverStateP, TmpDataP, TrailP, VsidsP, WatchlistsP,
};
use crate::lit::Lit;
use crate::proof::{self, DeleteClauseProof, ProofStep};
use crate::prop::{assignment, full_restart, Reason};
use crate::simplify::resurrect_unit;
use crate::state::SatState;

use crate::vec_mut_scan::VecMutScan;

/// Adds a clause to the current formula.
///
/// Removes duplicated literals, ignores tautological clauses (eg. x v -x v y), handles empty
/// clauses and dispatches among unit, binary and long clauses.
///
/// Does not adjust the solvers variable count. If necessary that has to be done before calling
/// this.
pub fn load_clause<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut IncrementalP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpDataP,
        mut TrailP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    lits: &[Lit],
) {
    match ctx.part(SolverStateP).sat_state {
        SatState::Unsat => return,
        SatState::Sat => {
            ctx.part_mut(SolverStateP).sat_state = SatState::Unknown;
        }
        _ => {}
    }

    ctx.part_mut(SolverStateP).formula_is_empty = false;

    // Restart the search when the user adds new clauses.
    full_restart(ctx.borrow());

    let (tmp_data, mut ctx) = ctx.split_part_mut(TmpDataP);

    tmp_data.lits.clear();
    tmp_data.lits.extend_from_slice(lits);
    let lits = &mut tmp_data.lits;
    let false_lits = &mut tmp_data.lits_2;

    lits.sort_unstable();
    lits.dedup();

    proof::add_clause(ctx.borrow(), &lits);

    // Detect tautological clauses
    let mut last = None;

    for &lit in lits.iter() {
        if last == Some(!lit) {
            proof::add_step(
                ctx.borrow(),
                &ProofStep::DeleteClause {
                    clause: lits,
                    proof: DeleteClauseProof::Satisfied,
                },
            );
            return;
        }
        last = Some(lit);
    }

    // Remove satisfied clauses and handle false literals.
    //
    // Proof generation expects us to start with the actual input clauses. If we would remove false
    // literals we would have to generate proof steps for that. This would result in derived clauses
    // being added during loading. If we're running proof processors on the fly, they'd see those
    // derived clauses interspersed with the input clauses.
    //
    // We don't want to require each proof processor to handle dervied clause additions during
    // loading of the initial formula. Thus we need to handle clauses with false literals here.
    false_lits.clear();

    let mut lits_scan = VecMutScan::new(lits);

    let mut clause_is_true = false;

    // We move unassigned literals to the beginning to make sure we're going to watch unassigned
    // literals.
    while let Some(lit) = lits_scan.next() {
        match ctx.part(AssignmentP).lit_value(*lit) {
            Some(true) => {
                clause_is_true = true;
                break;
            }
            Some(false) => {
                false_lits.push(lit.remove());
            }
            None => (),
        }
    }

    drop(lits_scan);

    let will_conflict = lits.is_empty();

    // We resurrect any removed false literals to ensure propagation by this new clause. This is
    // also required to eventually simplify this clause.
    for &lit in false_lits.iter() {
        resurrect_unit(ctx.borrow(), !lit);
    }

    lits.extend_from_slice(&false_lits);

    if clause_is_true {
        if lits.len() > 1 {
            proof::add_step(
                ctx.borrow(),
                &ProofStep::DeleteClause {
                    clause: lits,
                    proof: DeleteClauseProof::Satisfied,
                },
            );
        }
        return;
    }

    match lits[..] {
        [] => ctx.part_mut(SolverStateP).sat_state = SatState::Unsat,
        [lit] => {
            if will_conflict {
                ctx.part_mut(SolverStateP).sat_state = SatState::Unsat
            } else {
                assignment::enqueue_assignment(ctx.borrow(), lit, Reason::Unit)
            }
        }
        [lit_0, lit_1] => {
            ctx.part_mut(BinaryClausesP)
                .add_binary_clause([lit_0, lit_1]);
        }
        _ => {
            let mut header = ClauseHeader::new();
            header.set_tier(Tier::Irred);

            db::add_clause(ctx.borrow(), header, lits);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use partial_ref::IntoPartialRefMut;

    use crate::clause::Tier;
    use crate::context::set_var_count;

    #[test]
    fn unsat_on_empty_clause() {
        let mut ctx = Context::default();
        let mut ctx = ctx.into_partial_ref_mut();

        set_var_count(ctx.borrow(), 10);

        load_clause(ctx.borrow(), &[]);

        assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unsat);
    }

    #[test]
    fn unit_clauses() {
        let mut ctx = Context::default();
        let mut ctx = ctx.into_partial_ref_mut();

        set_var_count(ctx.borrow(), 10);

        load_clause(ctx.borrow(), &lits![1]);

        assert_eq!(ctx.part(TrailP).trail().len(), 1);

        load_clause(ctx.borrow(), &lits![3, -3]);

        assert_eq!(ctx.part(TrailP).trail().len(), 1);

        load_clause(ctx.borrow(), &lits![-2]);

        assert_eq!(ctx.part(TrailP).trail().len(), 2);

        load_clause(ctx.borrow(), &lits![1, 1]);

        assert_eq!(ctx.part(TrailP).trail().len(), 2);

        assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);

        load_clause(ctx.borrow(), &lits![2]);

        assert_eq!(ctx.part(TrailP).trail().len(), 2);

        assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unsat);
    }

    #[test]
    fn binary_clauses() {
        let mut ctx = Context::default();
        let mut ctx = ctx.into_partial_ref_mut();

        set_var_count(ctx.borrow(), 10);

        load_clause(ctx.borrow(), &lits![1, 2]);

        assert_eq!(ctx.part(BinaryClausesP).count(), 1);

        load_clause(ctx.borrow(), &lits![-1, 3, 3]);

        assert_eq!(ctx.part(BinaryClausesP).count(), 2);

        load_clause(ctx.borrow(), &lits![4, -4]);

        assert_eq!(ctx.part(BinaryClausesP).count(), 2);

        assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);
    }

    #[test]
    fn long_clauses() {
        let mut ctx = Context::default();
        let mut ctx = ctx.into_partial_ref_mut();

        set_var_count(ctx.borrow(), 10);

        load_clause(ctx.borrow(), &lits![1, 2, 3]);

        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Irred), 1);

        load_clause(ctx.borrow(), &lits![-2, 3, 3, 4]);

        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Irred), 2);

        load_clause(ctx.borrow(), &lits![4, -5, 5, 2]);

        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Irred), 2);

        assert_eq!(ctx.part(SolverStateP).sat_state, SatState::Unknown);
    }
}
