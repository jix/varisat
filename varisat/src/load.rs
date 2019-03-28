//! Loading a formula into the solver.
use partial_ref::{partial, PartialRef};

use crate::clause::{db, ClauseHeader, Tier};
use crate::context::{
    AssignmentP, BinaryClausesP, ClauseAllocP, ClauseDbP, Context, ImplGraphP, IncrementalP,
    ProofP, SolverStateP, TmpDataP, TrailP, VsidsP, WatchlistsP,
};
use crate::lit::Lit;
use crate::proof::{clause_hash, ProofStep};
use crate::prop::{assignment, full_restart, Reason};
use crate::state::SatState;

/// Adds a clause to the current formula.
///
/// Removes duplicated literals, ignores tautological clauses (eg. x v -x v y), handles empty
/// clauses and dispatches among unit, binary and long clauses.
///
/// Does not adjust the solvers variable count. If necessary that has to be done before calling
/// this.
pub fn load_clause(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ClauseAllocP,
        mut ClauseDbP,
        mut ImplGraphP,
        mut IncrementalP,
        mut ProofP,
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

    // Restart the search when the user adds new clauses.
    full_restart(ctx.borrow());

    let (tmp_data, mut ctx) = ctx.split_part_mut(TmpDataP);
    let (proof, mut ctx) = ctx.split_part_mut(ProofP);

    tmp_data.lits.clear();
    tmp_data.lits.extend_from_slice(lits);
    let lits = &mut tmp_data.lits;
    let simplified_lits = &mut tmp_data.lits_2;

    lits.sort_unstable();
    lits.dedup();

    // Detect tautological clauses
    let mut last = None;

    for &lit in lits.iter() {
        if last == Some(!lit) {
            proof.add_step(&ProofStep::DeleteClause(lits[..].into()));
            return;
        }
        last = Some(lit);
    }

    // Remove false literals and satisfied clauses
    simplified_lits.clear();

    for &lit in lits.iter() {
        match ctx.part(AssignmentP).lit_value(lit) {
            Some(true) => {
                proof.add_step(&ProofStep::DeleteClause(lits[..].into()));
                return;
            }
            Some(false) => (),
            None => {
                simplified_lits.push(lit);
            }
        }
    }

    if proof.is_active() && simplified_lits.len() < lits.len() {
        let hash = [clause_hash(lits)];
        proof.add_step(&ProofStep::RupClause(
            simplified_lits[..].into(),
            hash[..].into(),
        ));
        proof.add_step(&ProofStep::DeleteClause(lits[..].into()));
    }

    match simplified_lits[..] {
        [] => ctx.part_mut(SolverStateP).sat_state = SatState::Unsat,
        [lit] => assignment::enqueue_assignment(ctx.borrow(), lit, Reason::Unit),
        [lit_0, lit_1] => {
            ctx.part_mut(BinaryClausesP)
                .add_binary_clause([lit_0, lit_1]);
        }
        _ => {
            let mut header = ClauseHeader::new();
            header.set_tier(Tier::Irred);

            db::add_clause(ctx.borrow(), header, simplified_lits);
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
