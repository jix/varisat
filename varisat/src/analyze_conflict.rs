//! Learns a new clause by analyzing a conflict.
use std::mem::swap;

use partial_ref::{partial, split_borrow, PartialRef};

use crate::clause::ClauseRef;
use crate::context::{AnalyzeConflictP, ClauseAllocP, Context, ImplGraphP, ProofP, TrailP, VsidsP};
use crate::lit::{Lit, LitIdx, Var};
use crate::proof::{clause_hash, lit_hash, ClauseHash};
use crate::prop::{Conflict, Reason};

use crate::vec_mut_scan::VecMutScan;

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
    /// Clauses to bump.
    involved: Vec<ClauseRef>,
    /// Hashes of all involved clauses needed to proof the minimized clause.
    clause_hashes: Vec<ClauseHash>,
    /// Clause hashes paired with the trail depth of the propagated lit.
    unordered_clause_hashes: Vec<(LitIdx, ClauseHash)>,
    /// Stack for recursive minimization.
    stack: Vec<Lit>,
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

    /// Long clauses involved in the conflict.
    pub fn involved(&self) -> &[ClauseRef] {
        &self.involved
    }

    /// Hashes of clauses involved in the proof of the learned clause.
    ///
    /// Hashes are in clause propagation order.
    pub fn clause_hashes(&self) -> &[ClauseHash] {
        &self.clause_hashes
    }
}

/// Learns a new clause by analyzing a conflict.
///
/// Returns the lowest decision level that makes the learned clause asserting.
pub fn analyze_conflict(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut VsidsP,
        ClauseAllocP,
        ImplGraphP,
        ProofP,
        TrailP,
    ),
    conflict: Conflict,
) -> usize {
    split_borrow!(lit_ctx = &(ClauseAllocP) ctx);

    {
        let analyze = ctx.part_mut(AnalyzeConflictP);

        analyze.clause.clear();
        analyze.involved.clear();
        analyze.clause_hashes.clear();
        analyze.unordered_clause_hashes.clear();
        analyze.current_level_count = 0;
    }

    // We start with all the literals of the conflicted clause
    let conflict_lits = conflict.lits(&lit_ctx);

    if ctx.part(ProofP).clause_hashes_required() {
        ctx.part_mut(AnalyzeConflictP)
            .clause_hashes
            .push(clause_hash(conflict_lits));
    }

    if ctx.part(TrailP).current_level() == 0 {
        // Conflict with no decisions, generate empty clause
        return 0;
    }

    for &lit in conflict_lits {
        add_literal(ctx.borrow(), lit);
    }

    if let Conflict::Long(cref) = conflict {
        ctx.part_mut(AnalyzeConflictP).involved.push(cref);
    }

    // To get rid of all but one literal of the current level, we resolve the clause with the reason
    // for those literals. The correct order for this is reverse chronological.

    split_borrow!(ctx_trail = &(TrailP) ctx);
    // split_borrow!(ctx_analyze = &(mut AnalyzeConflictP) ctx);

    for &lit in ctx_trail.part(TrailP).trail().iter().rev() {
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
                let (graph, mut ctx) = ctx.split_part(ImplGraphP);

                let reason = graph.reason(lit.var());

                let lits = reason.lits(&lit_ctx);

                if ctx.part(ProofP).clause_hashes_required() && !reason.is_unit() {
                    let hash = clause_hash(lits) ^ lit_hash(lit);
                    ctx.part_mut(AnalyzeConflictP).clause_hashes.push(hash);
                }

                for &lit in lits {
                    add_literal(ctx.borrow(), lit);
                }

                if let &Reason::Long(cref) = reason {
                    ctx.part_mut(AnalyzeConflictP).involved.push(cref);
                }
            }
        }
    }

    // This needs var_flags set and keeps some var_fags set.
    minimize_clause(ctx.borrow());

    let (analyze, mut ctx) = ctx.split_part_mut(AnalyzeConflictP);

    if ctx.part(ProofP).clause_hashes_required() {
        // Clause minimization cannot give us clause hashes in propagation order, so we need to sort
        // them. Clauses used during minimization propagte before clauses used during initial
        // analysis. The clauses during initial analysis are discovered in reverse propagation
        // order. This means we can sort the minimization clauses in reverse order, append them to
        // the initial clauses and then reverse the order of all clauses.
        analyze
            .unordered_clause_hashes
            .sort_unstable_by_key(|&(depth, _)| !depth);

        analyze
            .unordered_clause_hashes
            .dedup_by_key(|&mut (depth, _)| depth);

        analyze.clause_hashes.extend(
            analyze
                .unordered_clause_hashes
                .iter()
                .map(|&(_, hash)| hash),
        );
        analyze.clause_hashes.reverse();
    }

    for var in analyze.to_clean.drain(..) {
        analyze.var_flags[var.index()] = false;
    }

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

    ctx.part_mut(VsidsP).decay();

    backtrack_to
}

/// Add a literal to the current clause.
fn add_literal(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut VsidsP,
        ImplGraphP,
        TrailP
    ),
    lit: Lit,
) {
    let (analyze, mut ctx) = ctx.split_part_mut(AnalyzeConflictP);
    let lit_level = ctx.part(ImplGraphP).level(lit.var());
    // No need to add literals that are set by unit clauses or already present
    if lit_level > 0 && !analyze.var_flags[lit.index()] {
        ctx.part_mut(VsidsP).bump(lit.var());

        analyze.var_flags[lit.index()] = true;
        if lit_level == ctx.part(TrailP).current_level() {
            analyze.current_level_count += 1;
        } else {
            analyze.clause.push(lit);
            analyze.to_clean.push(lit.var());
        }
    }
}

/// A Bloom filter of levels.
#[derive(Default)]
struct LevelAbstraction {
    bits: u64,
}

impl LevelAbstraction {
    /// Add a level to the Bloom filter.
    pub fn add(&mut self, level: usize) {
        self.bits |= 1 << (level % 64)
    }

    /// Test whether a level could be in the Bloom filter.
    pub fn test(&self, level: usize) -> bool {
        self.bits & (1 << (level % 64)) != 0
    }
}

/// Performs recursive clause minimization.
///
/// **Note:** Requires AnalyzeConflict's var_flags to be set for exactly the variables of the
/// unminimized claused. This also sets some more var_flags, but lists them in to_clean.
///
/// This routine tries to remove some redundant literals of the learned clause. The idea is to
/// detect literals of the learned clause that are already implied by other literals of the clause.
///
/// This is done by performing a DFS in the implication graph (following edges in reverse) for each
/// literal (apart from the asserting one). The search doesn't expand literals already known to be
/// implied by literals of the clause. When a decision literal that is not in the clause is found,
/// it means that the literal is not redundant.
///
/// There are two optimizations used here: The first one is to stop the search as soon as a literal
/// of a decision level not present in the clause is found. If the DFS would be continued it would
/// at some point reach the decision of that level. That decision belongs to a level not in the
/// clause and thus itself can't be in the clause. Checking whether the decision level is among the
/// clause's decision levels is done approximately using a Bloom filter.
///
/// The other optimization is to avoid duplicating work during the DFS searches. When one literal is
/// found to be redundant that means the whole search stayed within the implied literals. We
/// remember this and will not expand any of these literals for the following DFS searches.
///
/// In this implementation the var_flags array here has two purposes. At the beginning it is set for
/// all the literals of the clause. It is also used to mark the literals visited during the DFS.
/// This allows us to combine the already-visited-check with the literal-present-in-clause check. It
/// also allows for a neat implementation of the second optimization. When the search finds the
/// literal to be non-redundant, we clear var_flags for the literals we visited, resetting it to the
/// state at the beginning of the DFS. When the literal was redundant we keep it as is. This means
/// the following DFS will not expand these literals.
fn minimize_clause(
    mut ctx: partial!(
        Context,
        mut AnalyzeConflictP,
        mut VsidsP,
        ClauseAllocP,
        ImplGraphP,
        ProofP,
        TrailP,
    ),
) {
    let (analyze, mut ctx) = ctx.split_part_mut(AnalyzeConflictP);
    split_borrow!(lit_ctx = &(ClauseAllocP) ctx);
    let impl_graph = ctx.part(ImplGraphP);

    let mut involved_levels = LevelAbstraction::default();

    for &lit in analyze.clause.iter() {
        involved_levels.add(impl_graph.level(lit.var()));
    }

    let mut scan = VecMutScan::new(&mut analyze.clause);

    // we always keep the first literal
    scan.next();

    'next_lit: while let Some(lit) = scan.next() {
        if impl_graph.reason(lit.var()) == &Reason::Unit {
            continue;
        }

        // Start the DFS
        analyze.stack.clear();
        analyze.stack.push(!*lit);

        // Used to remember which var_flags are set during this DFS
        let top = analyze.to_clean.len();

        // Used to remember which clause hashes were added during the DFS, so we can remove them in
        // case the literal is not redundant.
        let hashes_top = analyze.unordered_clause_hashes.len();

        while let Some(lit) = analyze.stack.pop() {
            let reason = impl_graph.reason(lit.var());
            let lits = reason.lits(&lit_ctx);

            if ctx.part(ProofP).clause_hashes_required() && !reason.is_unit() {
                let depth = impl_graph.depth(lit.var()) as LitIdx;
                let hash = clause_hash(lits) ^ lit_hash(lit);
                analyze.unordered_clause_hashes.push((depth, hash));
            }

            for &reason_lit in lits {
                let reason_level = impl_graph.level(reason_lit.var());

                if !analyze.var_flags[reason_lit.index()] && reason_level > 0 {
                    // We haven't established reason_lit to be redundant, haven't visited it yet and
                    // it's not implied by unit clauses.

                    if impl_graph.reason(reason_lit.var()) == &Reason::Unit
                        || !involved_levels.test(reason_level)
                    {
                        // reason_lit is a decision not in the clause or in a decision level known
                        // not to be in the clause. Abort the search.

                        // Reset the var_flags set during _this_ DFS.
                        for lit in analyze.to_clean.drain(top..) {
                            analyze.var_flags[lit.index()] = false;
                        }
                        // Remove clauses not needed to justify the minimized clause.
                        analyze.unordered_clause_hashes.truncate(hashes_top);
                        continue 'next_lit;
                    } else {
                        analyze.var_flags[reason_lit.index()] = true;
                        analyze.to_clean.push(reason_lit.var());
                        analyze.stack.push(!reason_lit);
                    }
                }
            }
        }

        lit.remove();
    }
}
