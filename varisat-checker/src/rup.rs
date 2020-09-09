//! Reverse unit propagation redundancy checks.
use std::ops::Range;

use partial_ref::{partial, PartialRef};

use varisat_formula::{lit::LitIdx, Lit};
use varisat_internal_proof::ClauseHash;

use crate::{
    clauses::{UnitClause, UnitId},
    context::{parts::*, Context},
    hash::rehash,
    variables::ensure_var,
    CheckerError,
};

/// Propagation of the RUP check.
struct TraceItem {
    id: u64,
    edges: Range<usize>,
    unused: bool,
}

#[derive(Default)]
pub struct RupCheck {
    /// Stores overwritten values in `unit_clauses` to undo assignments.
    trail: Vec<(Lit, Option<UnitClause>)>,
    /// Involved clauses during the last check.
    trace: Vec<TraceItem>,
    /// Edges of the trace implication graph.
    trace_edges: Vec<LitIdx>,
    /// Just the ids of `trace`.
    pub trace_ids: Vec<u64>,
}

/// Check whether a clause is implied by clauses of the given hashes.
///
/// `lits` must be sorted and free of duplicates.
pub fn check_clause_with_hashes<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut ClauseHasherP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut RupCheckP,
        mut VariablesP,
        CheckerStateP,
    ),
    lits: &[Lit],
    propagation_hashes: &[ClauseHash],
) -> Result<(), CheckerError> {
    if ctx.part(ClauseHasherP).rename_in_buffered_solver_var_names {
        // TODO partial rehashing?
        rehash(ctx.borrow());
    }

    let (rup, mut ctx) = ctx.split_part_mut(RupCheckP);

    rup.trace.clear();
    rup.trace_edges.clear();

    let mut rup_is_unsat = false;

    assert!(rup.trail.is_empty());

    for &lit in lits.iter() {
        ensure_var(ctx.borrow(), lit.var());
    }

    let (clauses, ctx) = ctx.split_part_mut(ClausesP);

    for &lit in lits.iter() {
        if let Some((true, unit)) = clauses.lit_value(lit) {
            if let UnitId::Global(id) = unit.id {
                rup.trace_ids.clear();
                rup.trace_ids.push(id);
                return Ok(());
            } else {
                unreachable!("unexpected non global unit");
            }
        }
    }

    // Set all lits to false
    for &lit in lits.iter() {
        rup.trail.push((lit, clauses.unit_clauses[lit.index()]));

        clauses.unit_clauses[lit.index()] = Some(UnitClause {
            value: lit.is_negative(),
            id: UnitId::InClause,
        });
    }

    'hashes: for &hash in propagation_hashes.iter() {
        let candidates = match clauses.clauses.get(&hash) {
            Some(candidates) if !candidates.is_empty() => candidates,
            _ => {
                return Err(CheckerError::check_failed(
                    ctx.part(CheckerStateP).step,
                    format!("no clause found for hash {:x}", hash),
                ))
            }
        };

        // Check if any clause matching the hash propagates
        'candidates: for clause in candidates.iter() {
            let mut unassigned_count = 0;
            let mut unassigned_lit = None;

            let range_begin = rup.trace_edges.len();

            for &lit in clause.lits.slice(&clauses.literal_buffer).iter() {
                match clauses.lit_value(lit) {
                    Some((true, _)) => {
                        continue 'candidates;
                    }
                    Some((false, unit)) => match unit.id {
                        UnitId::Global(id) => {
                            rup.trail.push((lit, clauses.unit_clauses[lit.index()]));
                            clauses.unit_clauses[lit.index()] = Some(UnitClause {
                                value: lit.is_negative(),
                                id: UnitId::TracePos(rup.trace.len()),
                            });

                            rup.trace_edges.push(rup.trace.len() as LitIdx);

                            rup.trace.push(TraceItem {
                                id,
                                edges: 0..0,
                                unused: true,
                            });
                        }
                        UnitId::TracePos(pos) => {
                            rup.trace_edges.push(pos as LitIdx);
                        }
                        UnitId::InClause => {}
                    },
                    None => {
                        unassigned_count += 1;
                        unassigned_lit = Some(lit);
                    }
                }
            }

            let range = range_begin..rup.trace_edges.len();

            match unassigned_lit {
                None => {
                    rup.trace.push(TraceItem {
                        id: clause.id,
                        edges: range,
                        unused: false,
                    });

                    rup_is_unsat = true;
                    break 'hashes;
                }
                Some(lit) if unassigned_count == 1 => {
                    rup.trail.push((lit, clauses.unit_clauses[lit.index()]));

                    clauses.unit_clauses[lit.index()] = Some(UnitClause {
                        value: lit.is_positive(),
                        id: UnitId::TracePos(rup.trace.len()),
                    });

                    rup.trace.push(TraceItem {
                        id: clause.id,
                        edges: range,
                        unused: true,
                    });
                }
                _ => (),
            }
        }
    }

    if rup_is_unsat && !ctx.part(ProcessingP).processors.is_empty() {
        for i in (0..rup.trace.len()).rev() {
            if !rup.trace[i].unused {
                let edges = rup.trace[i].edges.clone();
                for &edge in rup.trace_edges[edges].iter() {
                    rup.trace[edge as usize].unused = false;
                }
            }
        }
        rup.trace_ids.clear();
        rup.trace_ids.extend(rup.trace.iter().map(|trace| trace.id));
    }

    // Undo temporary assignments
    for (lit, value) in rup.trail.drain(..).rev() {
        clauses.unit_clauses[lit.index()] = value;
    }

    if rup_is_unsat {
        Ok(())
    } else {
        Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("AT check failed for {:?}", lits),
        ))
    }
}
