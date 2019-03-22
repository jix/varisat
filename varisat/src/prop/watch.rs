//! Watchlists to detect clauses that became unit.
//!
//! Each (long) clause has always two watches pointing to it. The watches are kept in the watchlists
//! of two different literals of the clause. Whenever the watches are moved to different literals
//! the litereals of the clause are permuted so the watched literals are in position 0 and 1.
//!
//! When a clause is not unit under the current assignment, the watched literals point at two
//! non-false literals. When a clause is unit and thus propagating, the true literal is watched and
//! in position 0, the other watched literal is the one with the largest decision level and kept in
//! position 1. When a clause becomes satisfied before becoming unit the watches can be kept as they
//! were.
//!
//! When a literal is assigned false that invariant can be invalidated. This can be detected by
//! scanning the watches of the assigned literal. When the assignment is processed the watches are
//! moved to restore that invariant. Unless there is a conflict, i.e. a clause with no non-false
//! literals, this can always be done. This also finds all clauses that became unit. The new unit
//! clauses are exactly those clauses where no two non-false literals can be found.
//!
//! There is no need to update watchlists on backtracking, as unassigning variables cannot
//! invalidate the invariant.
//!
//! See [Section 4.5.1 of the "Handbook of Satisfiability"][handbook-ch4] for more details and
//! references.
//!
//! As a further optimization we use blocking literals. This means that each watch stores a literal
//! of the clause that is different from the watched literal. It can be the other watched literal or
//! any unwatched literal. When that literal is true, the clause is already satisfied, meaning that
//! no watches need to be updated. This can be detected by just looking at the watch, avoiding
//! access of the clause database. This variant was introduced by [Niklas Sörensson and Niklas Eén
//! in "MINISAT 2.1 and MINISAT++1.0 — SAT Race 2008 Editions"][minisat-2.1].
//!
//! [handbook-ch4]: https://www.satassociation.org/articles/FAIA185-0131.pdf
//! [minisat-2.1]: https://www.cril.univ-artois.fr/SAT09/solvers/booklet.pdf

use partial_ref::{partial, PartialRef};

use crate::clause::{db, ClauseRef};
use crate::context::{ClauseAllocP, ClauseDbP, Context, WatchlistsP};
use crate::lit::Lit;

/// A watch on a long clause.
#[derive(Copy, Clone)]
pub struct Watch {
    /// Clause which has the referring lit in position 0 or 1.
    pub cref: ClauseRef,
    /// A lit of the clause, different from the referring lit.
    pub blocking: Lit,
}

/// Watchlists to detect clauses that became unit.
pub struct Watchlists {
    /// Contains only valid data for indices of assigned variables.
    watches: Vec<Vec<Watch>>,
    /// Whether watchlists are present
    enabled: bool,
}

impl Default for Watchlists {
    fn default() -> Watchlists {
        Watchlists {
            watches: vec![],
            enabled: true,
        }
    }
}

impl Watchlists {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        self.watches.resize(count * 2, vec![]);
    }

    /// Start watching a clause.
    ///
    /// `lits` have to be the first two literals of the given clause.
    pub fn watch_clause(&mut self, cref: ClauseRef, lits: [Lit; 2]) {
        if !self.enabled {
            return;
        }

        for i in 0..2 {
            let watch = Watch {
                cref: cref,
                blocking: lits[i ^ 1],
            };
            self.add_watch(!lits[i], watch);
        }
    }

    /// Return watches for a given literal.
    pub fn watched_by_mut(&mut self, lit: Lit) -> &mut Vec<Watch> {
        &mut self.watches[lit.code()]
    }

    /// Make a literal watch a clause.
    pub fn add_watch(&mut self, lit: Lit, watch: Watch) {
        self.watches[lit.code()].push(watch)
    }

    /// Are watchlists enabled.
    pub fn enabled(&self) -> bool {
        self.enabled
    }

    /// Clear and disable watchlists.
    ///
    /// Actual clearing of the watchlists is done on re-enabling of the watchlists.
    pub fn disable(&mut self) {
        self.enabled = false;
    }
}

/// Enable and rebuild watchlists.
pub fn enable_watchlists(mut ctx: partial!(Context, mut WatchlistsP, ClauseAllocP, ClauseDbP)) {
    let (watchlists, mut ctx) = ctx.split_part_mut(WatchlistsP);
    if watchlists.enabled {
        return;
    }

    for watchlist in watchlists.watches.iter_mut() {
        watchlist.clear();
    }

    watchlists.enabled = true;

    let (alloc, mut ctx) = ctx.split_part(ClauseAllocP);

    for cref in db::clauses_iter(&ctx.borrow()) {
        let lits = alloc.clause(cref).lits();
        watchlists.watch_clause(cref, [lits[0], lits[1]]);
    }
}
