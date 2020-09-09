//! Checker state and checking of proof steps.

use std::io;
use std::mem::replace;

use hashbrown::HashSet;
use partial_ref::{partial, PartialRef};

use varisat_formula::{Lit, Var};
use varisat_internal_proof::{binary_format::Parser, ClauseHash, DeleteClauseProof, ProofStep};

use crate::clauses::{
    add_clause, delete_clause, store_clause, store_unit_clause, DeleteClauseResult,
    StoreClauseResult, UnitClause, UnitId,
};
use crate::context::{parts::*, Context};
use crate::hash::rehash;
use crate::processing::{
    process_step, CheckedProofStep, CheckedSamplingMode, CheckedUserVar, ResolutionPropagations,
};
use crate::rup::check_clause_with_hashes;
use crate::sorted_lits::{copy_canonical, is_subset};
use crate::variables::{
    add_user_mapping, ensure_sampling_var, ensure_var, remove_user_mapping, SamplingMode, VarData,
};
use crate::CheckerError;

/// A checker for unsatisfiability proofs in the native varisat format.
#[derive(Default)]
pub struct CheckerState {
    /// Current step number.
    pub step: u64,
    /// Whether unsatisfiability was proven.
    pub unsat: bool,
    /// Whether an end of proof step was checked.
    ended: bool,
    /// Last added irredundant clause id.
    ///
    /// Sorted and free of duplicates.
    previous_irred_clause_id: Option<u64>,
    /// Last added irredundant clause literals.
    previous_irred_clause_lits: Vec<Lit>,
    /// Current assumptions, used to check FailedAssumptions and Model
    assumptions: Vec<Lit>,
}

impl CheckerState {
    /// Check whether a given clause is subsumed by the last added irredundant clause.
    ///
    /// `lits` must be sorted and free of duplicates.
    fn subsumed_by_previous_irred_clause(&self, lits: &[Lit]) -> bool {
        if self.previous_irred_clause_id.is_none() {
            return false;
        }
        is_subset(&self.previous_irred_clause_lits[..], lits, true)
    }
}

/// Check a single proof step
pub fn check_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut CheckerStateP,
        mut ClauseHasherP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut RupCheckP,
        mut TmpDataP,
        mut VariablesP,
    ),
    step: ProofStep,
) -> Result<(), CheckerError> {
    let mut result = match step {
        ProofStep::SolverVarName { global, solver } => {
            ctx.part_mut(ClauseHasherP)
                .buffered_solver_var_names
                .push((global, solver));
            if solver.is_some() {
                ctx.part_mut(ClauseHasherP)
                    .rename_in_buffered_solver_var_names = true;
            }
            Ok(())
        }
        ProofStep::UserVarName { global, user } => {
            if let Some(user) = user {
                add_user_mapping(ctx.borrow(), global, user)?;
            } else {
                remove_user_mapping(ctx.borrow(), global)?;
            }
            Ok(())
        }
        ProofStep::DeleteVar { var } => check_delete_var_step(ctx.borrow(), var),
        ProofStep::ChangeSamplingMode { var, sample } => {
            check_change_sampling_mode(ctx.borrow(), var, sample)
        }
        ProofStep::AddClause { clause } => add_clause(ctx.borrow(), clause),
        ProofStep::AtClause {
            redundant,
            clause,
            propagation_hashes,
        } => check_at_clause_step(ctx.borrow(), redundant, clause, propagation_hashes),
        ProofStep::DeleteClause { clause, proof } => {
            check_delete_clause_step(ctx.borrow(), clause, proof)
        }
        ProofStep::UnitClauses { units } => check_unit_clauses_step(ctx.borrow(), units),
        ProofStep::ChangeHashBits { bits } => {
            ctx.part_mut(ClauseHasherP).hash_bits = bits;
            rehash(ctx.borrow());
            Ok(())
        }
        ProofStep::Model { assignment } => check_model_step(ctx.borrow(), assignment),
        ProofStep::Assumptions { assumptions } => {
            for &lit in assumptions.iter() {
                ensure_sampling_var(ctx.borrow(), lit.var())?;
            }
            copy_canonical(&mut ctx.part_mut(CheckerStateP).assumptions, assumptions);

            let (state, mut ctx) = ctx.split_part(CheckerStateP);

            process_step(
                ctx.borrow(),
                &CheckedProofStep::Assumptions {
                    assumptions: &state.assumptions,
                },
            )?;
            Ok(())
        }
        ProofStep::FailedAssumptions {
            failed_core,
            propagation_hashes,
        } => check_failed_assumptions_step(ctx.borrow(), failed_core, propagation_hashes),
        ProofStep::End => {
            ctx.part_mut(CheckerStateP).ended = true;
            Ok(())
        }
    };

    if let Err(CheckerError::CheckFailed {
        ref mut debug_step, ..
    }) = result
    {
        *debug_step = format!("{:?}", step)
    }
    result
}

/// Check a DeleteVar step
fn check_delete_var_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut VariablesP,
        CheckerStateP,
    ),
    var: Var,
) -> Result<(), CheckerError> {
    ensure_var(ctx.borrow(), var);
    if let Some(user_var) = ctx.part(VariablesP).var_data[var.index()].user_var {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!(
                "deleted variable {:?} corresponds to user variable {:?}",
                var, user_var
            ),
        ));
    }

    for &polarity in &[false, true] {
        if ctx.part(VariablesP).lit_data[var.lit(polarity).code()].clause_count > 0 {
            return Err(CheckerError::check_failed(
                ctx.part(CheckerStateP).step,
                format!("deleted variable {:?} still has clauses", var),
            ));
        }
    }

    if let Some(unit_clause) = ctx.part(ClausesP).unit_clauses[var.index()] {
        let clause = [var.lit(unit_clause.value)];

        let id = match unit_clause.id {
            UnitId::Global(id) => id,
            _ => unreachable!(),
        };

        process_step(
            ctx.borrow(),
            &CheckedProofStep::DeleteRatClause {
                id,
                keep_as_redundant: false,
                clause: &clause[..],
                pivot: clause[0],
                propagations: &ResolutionPropagations {},
            },
        )?;
        ctx.part_mut(ClausesP).unit_clauses[var.index()] = None;
    }

    ctx.part_mut(VariablesP).var_data[var.index()] = VarData::default();

    Ok(())
}

/// Check a ChangeSamplingMode step
fn check_change_sampling_mode<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut VariablesP,
        CheckerStateP,
    ),
    var: Var,
    sample: bool,
) -> Result<(), CheckerError> {
    ensure_var(ctx.borrow(), var);
    let mut ctx_in = ctx;
    let (variables, ctx) = ctx_in.split_part_mut(VariablesP);
    let var_data = &mut variables.var_data[var.index()];
    let sampling_mode = if sample {
        SamplingMode::Sample
    } else {
        SamplingMode::Witness
    };

    if var_data.sampling_mode != sampling_mode {
        var_data.sampling_mode = sampling_mode;

        if let Some(user_var) = var_data.user_var {
            let sampling_mode = if var_data.sampling_mode == SamplingMode::Witness {
                CheckedSamplingMode::Witness
            } else {
                CheckedSamplingMode::Sample
            };
            process_step(
                ctx_in.borrow(),
                &CheckedProofStep::UserVar {
                    var,
                    user_var: Some(CheckedUserVar {
                        user_var,
                        sampling_mode,
                        new_var: false,
                    }),
                },
            )?;
        } else if sampling_mode == SamplingMode::Sample {
            return Err(CheckerError::check_failed(
                ctx.part(CheckerStateP).step,
                format!("cannot sample hidden variable {:?}", var),
            ));
        }
    }

    Ok(())
}

/// Check an AtClause step
fn check_at_clause_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut CheckerStateP,
        mut ClauseHasherP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut RupCheckP,
        mut TmpDataP,
        mut VariablesP,
    ),
    redundant: bool,
    clause: &[Lit],
    propagation_hashes: &[ClauseHash],
) -> Result<(), CheckerError> {
    let mut tmp = replace(&mut ctx.part_mut(TmpDataP).tmp, vec![]);

    if copy_canonical(&mut tmp, clause) {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("clause {:?} is a tautology", tmp),
        ));
    }

    check_clause_with_hashes(ctx.borrow(), &tmp, &*propagation_hashes)?;

    let (id, added) = store_clause(ctx.borrow(), &tmp, redundant);

    if !redundant {
        let state = ctx.part_mut(CheckerStateP);
        state.previous_irred_clause_id = Some(id);
        state.previous_irred_clause_lits.clear();
        state.previous_irred_clause_lits.extend_from_slice(&tmp);
    }

    match added {
        StoreClauseResult::New => {
            let (rup_check, mut ctx) = ctx.split_part(RupCheckP);
            process_step(
                ctx.borrow(),
                &CheckedProofStep::AtClause {
                    id,
                    redundant,
                    clause: &tmp,
                    propagations: &rup_check.trace_ids,
                },
            )?;
        }
        StoreClauseResult::NewlyIrredundant => {
            process_step(
                ctx.borrow(),
                &CheckedProofStep::MakeIrredundant { id, clause: &tmp },
            )?;
        }
        StoreClauseResult::Duplicate => (),
    }

    ctx.part_mut(TmpDataP).tmp = tmp;

    Ok(())
}

/// Check a DeleteClause step
fn check_delete_clause_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut CheckerStateP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut TmpDataP,
        mut VariablesP,
        ClauseHasherP,
    ),
    clause: &[Lit],
    proof: DeleteClauseProof,
) -> Result<(), CheckerError> {
    let mut tmp = replace(&mut ctx.part_mut(TmpDataP).tmp, vec![]);

    if copy_canonical(&mut tmp, clause) {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("clause {:?} is a tautology", tmp),
        ));
    }

    let redundant = proof == DeleteClauseProof::Redundant;

    let mut subsumed_by = None;

    match proof {
        DeleteClauseProof::Redundant => (),
        DeleteClauseProof::Satisfied => {
            let is_subsumed = tmp.iter().any(|&lit| {
                if let Some((
                    true,
                    UnitClause {
                        id: UnitId::Global(id),
                        ..
                    },
                )) = ctx.part(ClausesP).lit_value(lit)
                {
                    subsumed_by = Some(id);
                    true
                } else {
                    false
                }
            });
            if !is_subsumed {
                return Err(CheckerError::check_failed(
                    ctx.part(CheckerStateP).step,
                    format!("deleted clause {:?} is not satisfied", clause),
                ));
            }
        }
        DeleteClauseProof::Simplified => {
            subsumed_by = ctx.part(CheckerStateP).previous_irred_clause_id;
            if !ctx
                .part(CheckerStateP)
                .subsumed_by_previous_irred_clause(&tmp)
            {
                return Err(CheckerError::check_failed(
                    ctx.part(CheckerStateP).step,
                    format!(
                        "deleted clause {:?} is not subsumed by previous clause {:?}",
                        clause,
                        ctx.part(CheckerStateP).previous_irred_clause_lits
                    ),
                ));
            }
        }
    }

    ctx.part_mut(CheckerStateP).previous_irred_clause_id = None;
    ctx.part_mut(CheckerStateP)
        .previous_irred_clause_lits
        .clear();

    let (id, deleted) = delete_clause(ctx.borrow(), &tmp, redundant)?;

    if redundant {
        match deleted {
            DeleteClauseResult::Removed => {
                process_step(
                    ctx.borrow(),
                    &CheckedProofStep::DeleteClause { id, clause: &tmp },
                )?;
            }
            DeleteClauseResult::Unchanged => (),
            DeleteClauseResult::NewlyRedundant => unreachable!(),
        }
    } else {
        match deleted {
            DeleteClauseResult::Removed | DeleteClauseResult::NewlyRedundant => {
                process_step(
                    ctx.borrow(),
                    &CheckedProofStep::DeleteAtClause {
                        id,
                        keep_as_redundant: deleted == DeleteClauseResult::NewlyRedundant,
                        clause: &tmp,
                        propagations: &[subsumed_by.unwrap()],
                    },
                )?;
            }
            DeleteClauseResult::Unchanged => (),
        }
    }

    ctx.part_mut(TmpDataP).tmp = tmp;
    Ok(())
}

/// Check a UnitClauses step
fn check_unit_clauses_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut CheckerStateP,
        mut ClauseHasherP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut RupCheckP,
        mut VariablesP,
    ),
    units: &[(Lit, ClauseHash)],
) -> Result<(), CheckerError> {
    for &(lit, hash) in units.iter() {
        ensure_var(ctx.borrow(), lit.var());

        let clause = [lit];
        let propagation_hashes = [hash];
        check_clause_with_hashes(ctx.borrow(), &clause[..], &propagation_hashes[..])?;

        let (id, added) = store_unit_clause(ctx.borrow(), lit);

        match added {
            StoreClauseResult::New => {
                let (rup_check, mut ctx) = ctx.split_part(RupCheckP);
                process_step(
                    ctx.borrow(),
                    &CheckedProofStep::AtClause {
                        id,
                        redundant: false,
                        clause: &clause,
                        propagations: &rup_check.trace_ids,
                    },
                )?;
            }
            StoreClauseResult::Duplicate => (),
            StoreClauseResult::NewlyIrredundant => unreachable!(),
        }
    }
    Ok(())
}

/// Check a Model step
fn check_model_step<'a>(
    mut ctx: partial!(Context<'a>, mut ProcessingP<'a>, CheckerStateP, ClausesP, VariablesP),
    model: &[Lit],
) -> Result<(), CheckerError> {
    let mut assignments = HashSet::new();

    for &lit in model.iter() {
        if let Some((false, _)) = ctx.part(ClausesP).lit_value(lit) {
            return Err(CheckerError::check_failed(
                ctx.part(CheckerStateP).step,
                format!("model assignment conflicts with unit clause {:?}", !lit),
            ));
        }
        if assignments.contains(&!lit) {
            return Err(CheckerError::check_failed(
                ctx.part(CheckerStateP).step,
                format!("model contains conflicting assignment {:?}", !lit),
            ));
        }
        assignments.insert(lit);
    }

    for &lit in ctx.part(CheckerStateP).assumptions.iter() {
        if !assignments.contains(&lit) {
            return Err(CheckerError::check_failed(
                ctx.part(CheckerStateP).step,
                format!("model does not contain assumption {:?}", lit),
            ));
        }
    }

    for (_, candidates) in ctx.part(ClausesP).clauses.iter() {
        for clause in candidates.iter() {
            let lits = clause.lits.slice(&ctx.part(ClausesP).literal_buffer);
            if !lits.iter().any(|lit| assignments.contains(&lit)) {
                return Err(CheckerError::check_failed(
                    ctx.part(CheckerStateP).step,
                    format!("model does not satisfy clause {:?}", lits),
                ));
            }
        }
    }

    process_step(ctx.borrow(), &CheckedProofStep::Model { assignment: model })?;

    Ok(())
}

/// Check a FailedAssumptions step
fn check_failed_assumptions_step<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut ClauseHasherP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut RupCheckP,
        mut TmpDataP,
        mut VariablesP,
        CheckerStateP,
    ),
    failed_core: &[Lit],
    propagation_hashes: &[ClauseHash],
) -> Result<(), CheckerError> {
    let mut tmp = replace(&mut ctx.part_mut(TmpDataP).tmp, vec![]);

    let direct_conflict = copy_canonical(&mut tmp, failed_core);

    if !is_subset(&tmp, &ctx.part(CheckerStateP).assumptions, false) {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            "failed core contains non-assumed variables".to_string(),
        ));
    }

    if direct_conflict {
        // we have x and not x among the assumptions, no need to check
        ctx.part_mut(RupCheckP).trace_ids.clear();
    } else {
        // invert the assumptions and check for an AT
        for lit in tmp.iter_mut() {
            *lit = !*lit;
        }
        check_clause_with_hashes(ctx.borrow(), &tmp, propagation_hashes)?;

        // we undo the inversion to report the correct checked proof step
        for lit in tmp.iter_mut() {
            *lit = !*lit;
        }
    }

    let (rup_check, mut ctx) = ctx.split_part(RupCheckP);
    process_step(
        ctx.borrow(),
        &CheckedProofStep::FailedAssumptions {
            failed_core: &tmp,
            propagations: &rup_check.trace_ids,
        },
    )?;

    ctx.part_mut(TmpDataP).tmp = tmp;

    Ok(())
}

/// Checks a proof in the native Varisat format.
pub fn check_proof<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut CheckerStateP,
        mut ClauseHasherP,
        mut ClausesP,
        mut ProcessingP<'a>,
        mut RupCheckP,
        mut TmpDataP,
        mut VariablesP,
    ),
    input: impl io::Read,
) -> Result<(), CheckerError> {
    let mut buffer = io::BufReader::new(input);
    let mut parser = Parser::default();

    while !ctx.part(CheckerStateP).ended {
        ctx.part_mut(CheckerStateP).step += 1;

        let step = ctx.part(CheckerStateP).step;

        if step % 100000 == 0 {
            log::info!("checking step {}k", step / 1000);
        }

        match parser.parse_step(&mut buffer) {
            Ok(step) => check_step(ctx.borrow(), step)?,
            Err(err) => match err.downcast::<io::Error>() {
                Ok(io_err) => {
                    if io_err.kind() == io::ErrorKind::UnexpectedEof {
                        return Err(CheckerError::ProofIncomplete { step });
                    } else {
                        return Err(CheckerError::IoError {
                            step,
                            cause: io_err,
                        });
                    }
                }
                Err(err) => return Err(CheckerError::ParseError { step, cause: err }),
            },
        }
    }

    process_unit_conflicts(ctx.borrow())
}

/// Process unit conflicts detected during clause loading.
pub fn process_unit_conflicts<'a>(
    mut ctx: partial!(Context<'a>, mut ProcessingP<'a>, ClausesP, VariablesP),
) -> Result<(), CheckerError> {
    let (clauses, mut ctx) = ctx.split_part(ClausesP);
    if let Some(ids) = &clauses.unit_conflict {
        let clause = &[];

        process_step(
            ctx.borrow(),
            &CheckedProofStep::AtClause {
                id: clauses.next_clause_id,
                redundant: false,
                clause,
                propagations: ids,
            },
        )?;
    }

    Ok(())
}
