//! Database for long clauses.
use partial_ref::{partial, PartialRef};

use super::{header::HEADER_LEN, ClauseAlloc, ClauseHeader, ClauseRef};

use crate::context::{ClauseAllocP, ClauseDbP, Context};
use crate::lit::Lit;

use std::mem::transmute;

/// Partitions of the clause database.
///
/// The long clauses are partitioned into 4 [`Tier`]s. This follows the approach described by
/// Chanseok Oh in ["Between SAT and UNSAT: The Fundamental Difference in CDCL
/// SAT"](https://doi.org/10.1007/978-3-319-24318-4_23), section 4.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum Tier {
    Irred = 0,
    Core = 1,
    Mid = 2,
    Local = 3,
}

impl Tier {
    /// Total number of tiers.
    pub const fn count() -> usize {
        4
    }

    /// Cast an index into the corresponding tier.
    pub unsafe fn from_index(index: usize) -> Tier {
        debug_assert!(index < Tier::count());
        transmute(index as u8)
    }
}

#[derive(Default)]
/// Database for long clauses.
///
/// Removal of clauses from the `clauses` and the `by_tier` fields can be delayed. The clause
/// header's deleted and tier fields need to be checked when iterating over these. `by_tier` may
/// also contain duplicate entries.
pub struct ClauseDb {
    /// May contain deleted clauses, see above
    clauses: Vec<ClauseRef>,
    /// May contain deleted and moved clauses, see above
    by_tier: [Vec<ClauseRef>; Tier::count()],
    /// These counts should always be up to date
    count_by_tier: [usize; Tier::count()],
    /// Size of deleted but not collected clauses
    garbage_size: usize,
}

impl ClauseDb {
    /// Add a long clause to the database.
    pub fn add_clause(
        mut ctx: partial!(Context, mut ClauseDbP, mut ClauseAllocP),
        header: ClauseHeader,
        lits: &[Lit],
    ) -> ClauseRef {
        let tier = header.tier();

        let cref = ctx.part_mut(ClauseAllocP).add_clause(header, lits);

        let db = ctx.part_mut(ClauseDbP);

        db.clauses.push(cref);
        db.by_tier[tier as usize].push(cref);
        db.count_by_tier[tier as usize] += 1;

        cref
    }

    /// Change the tier of a long clause.
    ///
    /// This is a noop for a clause already of the specified tier.
    pub fn set_tier(
        mut ctx: partial!(Context, mut ClauseDbP, mut ClauseAllocP),
        cref: ClauseRef,
        tier: Tier,
    ) {
        let (alloc, mut ctx) = ctx.split_part_mut(ClauseAllocP);
        let db = ctx.part_mut(ClauseDbP);

        let old_tier = alloc.header(cref).tier();
        if old_tier != tier {
            db.count_by_tier[old_tier as usize] -= 1;
            db.count_by_tier[tier as usize] += 1;

            alloc.header_mut(cref).set_tier(tier);
            db.by_tier[tier as usize].push(cref);
        }
    }

    /// Delete a long clause from the database.
    pub fn delete_clause(
        mut ctx: partial!(Context, mut ClauseDbP, mut ClauseAllocP),
        cref: ClauseRef,
    ) {
        let (alloc, mut ctx) = ctx.split_part_mut(ClauseAllocP);
        let db = ctx.part_mut(ClauseDbP);

        let header = alloc.header_mut(cref);

        debug_assert!(
            !header.deleted(),
            "delete_clause for already deleted clause"
        );

        header.set_deleted(true);

        db.count_by_tier[header.tier() as usize] -= 1;

        db.garbage_size += header.len() + HEADER_LEN;
    }

    /// The number of long clauses of a given tier.
    pub fn count_by_tier(&self, tier: Tier) -> usize {
        self.count_by_tier[tier as usize]
    }

    /// Perform a garbage collection of long clauses if necessary.
    pub fn collect_garbage(mut ctx: partial!(Context, mut ClauseDbP, mut ClauseAllocP)) {
        let alloc = ctx.part(ClauseAllocP);
        let db = ctx.part(ClauseDbP);

        // Collecting when a fixed fraction of the allocation is garbage amortizes collection costs.
        if db.garbage_size * 2 > alloc.buffer_size() {
            Self::collect_garbage_now(ctx.borrow());
        }
    }

    /// Unconditionally perform a garbage collection of long clauses.
    pub fn collect_garbage_now(mut ctx: partial!(Context, mut ClauseDbP, mut ClauseAllocP)) {
        let (db, mut ctx) = ctx.split_part_mut(ClauseDbP);
        let alloc = ctx.part(ClauseAllocP);

        assert!(
            db.garbage_size <= alloc.buffer_size(),
            "Inconsistent garbage tracking in ClauseDb"
        );
        let current_size = alloc.buffer_size() - db.garbage_size;

        // Allocating just the current size would lead to an immediate growing when new clauses are
        // learned, overallocating here avoids that.
        let mut new_alloc = ClauseAlloc::with_capacity(current_size * 2);

        let mut new_clauses = vec![];
        let mut new_by_tier: [Vec<_>; Tier::count()] = Default::default();

        // TODO Optimize order of clauses (benchmark this)

        for &cref in db.clauses.iter() {
            let clause = alloc.clause(cref);
            let header = clause.header().clone();

            let new_cref = new_alloc.add_clause(header, clause.lits());

            new_clauses.push(new_cref);
            new_by_tier[header.tier() as usize].push(new_cref);
        }

        *ctx.part_mut(ClauseAllocP) = new_alloc;
        db.clauses = new_clauses;
        db.by_tier = new_by_tier;
        db.garbage_size = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use partial_ref::IntoPartialRefMut;
    use proptest::*;

    use crate::cnf::strategy::*;

    #[test]
    fn set_tiers_and_deletes() {
        let mut ctx = Context::default();

        let mut ctx = ctx.into_partial_ref_mut();

        let clauses = cnf_formula![
            1, 2, 3;
            4, -5, 6;
            -2, 3, -4;
            -3, 5, 2, 7, 5;
        ];

        let tiers = vec![Tier::Irred, Tier::Core, Tier::Mid, Tier::Local];
        let new_tiers = vec![Tier::Irred, Tier::Local, Tier::Local, Tier::Core];

        let mut crefs = vec![];

        for (clause, &tier) in clauses.iter().zip(tiers.iter()) {
            let mut header = ClauseHeader::new();
            header.set_tier(tier);
            let cref = ClauseDb::add_clause(ctx.borrow(), header, clause);
            crefs.push(cref);
        }

        for (&cref, &tier) in crefs.iter().rev().zip(new_tiers.iter().rev()) {
            ClauseDb::set_tier(ctx.borrow(), cref, tier);
        }

        // We only check presence, as deletion from these lists is delayed
        assert!(ctx.part(ClauseDbP).by_tier[Tier::Irred as usize].contains(&crefs[0]));
        assert!(ctx.part(ClauseDbP).by_tier[Tier::Core as usize].contains(&crefs[3]));
        assert!(ctx.part(ClauseDbP).by_tier[Tier::Local as usize].contains(&crefs[1]));
        assert!(ctx.part(ClauseDbP).by_tier[Tier::Local as usize].contains(&crefs[2]));

        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Irred), 1);
        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Core), 1);
        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Mid), 0);
        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Local), 2);

        ClauseDb::delete_clause(ctx.borrow(), crefs[0]);
        ClauseDb::delete_clause(ctx.borrow(), crefs[2]);

        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Irred), 0);
        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Core), 1);
        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Mid), 0);
        assert_eq!(ctx.part(ClauseDbP).count_by_tier(Tier::Local), 1);
    }

    proptest! {
        #[test]
        fn garbage_collection(
            input_a in cnf_formula(1..100usize, 500..1000, 3..30),
            input_b in cnf_formula(1..100usize, 0..500, 3..30),
        ) {
            let mut ctx = Context::default();
            let mut ctx = ctx.into_partial_ref_mut();

            let mut crefs_a = vec![];
            let mut crefs_b = vec![];

            for lits in input_a.iter() {
                let header = ClauseHeader::new();
                let cref = ClauseDb::add_clause(ctx.borrow(), header, lits);
                crefs_a.push(cref);
            }

            for lits in input_b.iter() {
                let header = ClauseHeader::new();
                let cref = ClauseDb::add_clause(ctx.borrow(), header, lits);
                crefs_b.push(cref);
            }

            for cref in crefs_a {
                ClauseDb::delete_clause(ctx.borrow(), cref);
                prop_assert!(ctx.part(ClauseDbP).garbage_size > 0);
                ClauseDb::collect_garbage(ctx.borrow());
            }

            prop_assert!(
                ctx.part(ClauseDbP).garbage_size * 2 < ctx.part(ClauseAllocP).buffer_size()
            );

            for (lits, &cref) in input_b.iter().zip(crefs_b.iter()) {
                prop_assert_eq!(ctx.part(ClauseAllocP).clause(cref).lits(), lits);
            }
        }
    }
}
