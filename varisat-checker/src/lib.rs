//! Proof checker for Varisat proofs.

use std::io;

use failure::{Error, Fail};

use varisat_dimacs::DimacsParser;
use varisat_formula::{CnfFormula, Lit, Var};

pub mod internal;

mod context;
mod state;
mod transcript;

pub use transcript::{ProofTranscriptProcessor, ProofTranscriptStep};

use context::Context;

/// Possible errors while checking a varisat proof.
#[derive(Debug, Fail)]
pub enum CheckerError {
    #[fail(display = "step {}: Unexpected end of proof file", step)]
    ProofIncomplete { step: u64 },
    #[fail(display = "step {}: Error reading proof file: {}", step, cause)]
    IoError {
        step: u64,
        #[cause]
        cause: io::Error,
    },
    #[fail(display = "step {}: Could not parse proof step: {}", step, cause)]
    ParseError {
        step: u64,
        #[cause]
        cause: Error,
    },
    #[fail(display = "step {}: Checking proof failed: {}", step, msg)]
    CheckFailed {
        step: u64,
        msg: String,
        debug_step: String,
    },
    #[fail(display = "Error in proof processor: {}", cause)]
    ProofProcessorError {
        #[cause]
        cause: Error,
    },
    #[doc(hidden)]
    #[fail(display = "__Nonexhaustive")]
    __Nonexhaustive,
}

impl CheckerError {
    /// Generate a CheckFailed error with an empty debug_step
    fn check_failed(step: u64, msg: String) -> CheckerError {
        CheckerError::CheckFailed {
            step,
            msg,
            debug_step: String::new(),
        }
    }
}

/// A single step of a proof.
///
/// Clauses are identified by a unique increasing id assigned by the checker. Whenever the literals
/// of a clause are included in a step, they are sorted and free of duplicates.
#[derive(Debug)]
pub enum CheckedProofStep<'a> {
    /// Updates the corresponding user variable for a proof variable.
    UserVar {
        var: Var,
        user_var: Option<CheckedUserVar>,
    },
    /// A clause of the input formula.
    AddClause { id: u64, clause: &'a [Lit] },
    /// A duplicated clause of the input formula.
    ///
    /// The checker detects duplicated clauses and will use the same id for all copies. This also
    /// applies to clauses of the input formula. This step allows proof processors to identify the
    /// input formula's clauses by consecutive ids. When a duplicate clause is found, an id is
    /// allocated and this step is emitted. The duplicated clause is not considered part of the
    /// formula and the allocated id will not be used in any other steps.
    DuplicatedClause {
        id: u64,
        same_as_id: u64,
        clause: &'a [Lit],
    },
    /// A tautological clause of the input formula.
    ///
    /// Tautological clauses can be completely ignored. This step is only used to give an id to a
    /// tautological input clause.
    TautologicalClause { id: u64, clause: &'a [Lit] },
    /// Addition of an asymmetric tautology (AT).
    ///
    /// A clause C is an asymmetric tautology wrt. a formula F, iff unit propagation in F with the
    /// negated literals of C as unit clauses leads to a conflict. The `propagations` field contains
    /// clauses in the order they became unit and as last element the clause that caused a conflict.
    AtClause {
        id: u64,
        redundant: bool,
        clause: &'a [Lit],
        propagations: &'a [u64],
    },
    /// Deletion of a redundant clause.
    DeleteClause { id: u64, clause: &'a [Lit] },
    /// Deletion of a clause that is an asymmetric tautology w.r.t the remaining irredundant
    /// clauses.
    DeleteAtClause {
        id: u64,
        keep_as_redundant: bool,
        clause: &'a [Lit],
        propagations: &'a [u64],
    },
    /// Deletion of a resolution asymmetric tautology w.r.t the remaining irredundant caluses.
    ///
    /// The pivot is always a hidden variable.
    DeleteRatClause {
        id: u64,
        keep_as_redundant: bool,
        clause: &'a [Lit],
        pivot: Lit,
        propagations: &'a ResolutionPropagations,
    },
    /// Make a redundant clause irredundant.
    MakeIrredundant { id: u64, clause: &'a [Lit] },
    /// A (partial) assignment that satisfies all clauses and assumptions.
    Model { assignment: &'a [Lit] },
    /// Change the active set of assumptions.
    Assumptions { assumptions: &'a [Lit] },
    /// Subset of assumptions incompatible with the formula.
    ///
    /// The proof consists of showing that the negation of the assumptions is an AT wrt. the
    /// formula.
    FailedAssumptions {
        failed_core: &'a [Lit],
        propagations: &'a [u64],
    },
}

/// Sampling mode of a user variable.
#[derive(Debug)]
pub enum CheckedSamplingMode {
    Sample,
    Witness,
}

/// Corresponding user variable for a proof variable.
#[derive(Debug)]
pub struct CheckedUserVar {
    user_var: Var,
    sampling_mode: CheckedSamplingMode,
    new_var: bool,
}

/// A list of clauses to resolve and propagations to show that the resolvent is an AT.
#[derive(Debug)]
pub struct ResolutionPropagations {
    // TODO implement ResolutionPropagations
}

/// Checker data available to proof processors.
#[derive(Copy, Clone)]
pub struct CheckerData<'a> {
    var_data: &'a [state::VarData],
}

impl<'a> CheckerData<'a> {
    /// User variable corresponding to proof variable.
    ///
    /// Returns `None` if the proof variable is an internal or hidden variable.
    pub fn user_from_proof_var(&self, proof_var: Var) -> Option<Var> {
        self.var_data.get(proof_var.index()).and_then(|var_data| {
            var_data.user_var.or_else(|| {
                // This is needed as yet another workaround to enable independently loading the
                // initial formula and proof.
                // TODO can this be solved in a better way?
                if var_data.sampling_mode == state::SamplingMode::Sample {
                    Some(proof_var)
                } else {
                    None
                }
            })
        })
    }
}

/// Implement to process proof steps.
pub trait ProofProcessor {
    fn process_step(&mut self, step: &CheckedProofStep, data: CheckerData) -> Result<(), Error>;
}

/// A checker for unsatisfiability proofs in the native varisat format.
#[derive(Default)]
pub struct Checker<'a> {
    ctx: Box<Context<'a>>,
}

impl<'a> Checker<'a> {
    /// Create a new checker.
    pub fn new() -> Checker<'a> {
        Checker::default()
    }

    /// Adds a clause to the checker.
    pub fn add_clause(&mut self, clause: &[Lit]) -> Result<(), CheckerError> {
        self.ctx.checker_state.add_clause(clause)
    }

    /// Add a formula to the checker.
    pub fn add_formula(&mut self, formula: &CnfFormula) -> Result<(), CheckerError> {
        for clause in formula.iter() {
            self.add_clause(clause)?;
        }

        Ok(())
    }

    /// Reads and adds a formula in DIMACS CNF format.
    ///
    /// Using this avoids creating a temporary [`CnfFormula`](varisat_formula::CnfFormula).
    pub fn add_dimacs_cnf(&mut self, input: impl io::Read) -> Result<(), Error> {
        let parser = DimacsParser::parse_incremental(input, |parser| {
            Ok(self.add_formula(&parser.take_formula())?)
        })?;

        log::info!(
            "Parsed formula with {} variables and {} clauses",
            parser.var_count(),
            parser.clause_count()
        );

        Ok(())
    }

    /// Add a [`ProofProcessor`].
    ///
    /// This has to be called before loading any clauses or checking any proofs.
    pub fn add_processor(&mut self, processor: &'a mut dyn ProofProcessor) {
        self.ctx.checker_state.processing.processors.push(processor);
    }

    /// Add a [`ProofTranscriptProcessor`].
    ///
    /// This has to be called before loading any clauses or checking any proofs.
    pub fn add_transcript(&mut self, processor: &'a mut dyn ProofTranscriptProcessor) {
        self.ctx
            .checker_state
            .processing
            .transcript_processors
            .push(processor);
    }

    /// Checks a proof in the native Varisat format.
    pub fn check_proof(&mut self, input: impl io::Read) -> Result<(), CheckerError> {
        self.ctx.checker_state.check_proof(input)
    }
}

#[cfg(test)]
mod tests {
    use super::internal::SelfChecker;
    use super::*;

    use varisat_internal_proof::{DeleteClauseProof, ProofStep};

    use varisat_formula::{cnf_formula, lits};

    fn expect_check_failed(result: Result<(), CheckerError>, contains: &str) {
        match result {
            Err(CheckerError::CheckFailed { ref msg, .. }) if msg.contains(contains) => (),
            err => panic!("expected {:?} error but got {:?}", contains, err),
        }
    }

    #[test]
    fn conflicting_units() {
        let mut checker = Checker::new();

        checker
            .add_formula(&cnf_formula![
                1;
                -1;
            ])
            .unwrap();

        assert!(checker.ctx.checker_state.unsat);
    }

    #[test]
    fn invalid_delete() {
        let mut checker = Checker::new();

        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -4, 5;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: &lits![-5, 4],
                proof: DeleteClauseProof::Redundant,
            }),
            "unknown clause",
        );
    }

    #[test]
    fn ref_counts() {
        let mut checker = Checker::new();

        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                1, 2, 3;
                1;
            ])
            .unwrap();

        let lits = &lits![1, 2, 3][..];

        checker
            .self_check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            })
            .unwrap();

        checker.add_clause(lits).unwrap();

        checker
            .self_check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: lits,
                proof: DeleteClauseProof::Satisfied,
            }),
            "unknown clause",
        );
    }

    #[test]
    fn clause_not_found() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::AtClause {
                redundant: false,
                clause: [][..].into(),
                propagation_hashes: [0][..].into(),
            }),
            "no clause found",
        )
    }

    #[test]
    fn clause_check_failed() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::AtClause {
                redundant: false,
                clause: [][..].into(),
                propagation_hashes: [][..].into(),
            }),
            "AT check failed",
        )
    }

    #[test]
    fn add_derived_tautology() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::AtClause {
                redundant: false,
                clause: &lits![-3, 3],
                propagation_hashes: &[],
            }),
            "tautology",
        )
    }

    #[test]
    fn delete_derived_tautology() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                -3, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: &lits![-3, 3],
                proof: DeleteClauseProof::Redundant,
            }),
            "tautology",
        )
    }

    #[test]
    fn delete_unit_clause() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: &lits![1],
                proof: DeleteClauseProof::Redundant,
            }),
            "delete of unit or empty clause",
        )
    }

    #[test]
    fn delete_clause_not_redundant() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: &lits![1, 2, 3],
                proof: DeleteClauseProof::Redundant,
            }),
            "is irredundant",
        )
    }

    #[test]
    fn delete_clause_not_satisfied() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -2;
                4;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: &lits![1, 2, 3],
                proof: DeleteClauseProof::Satisfied,
            }),
            "not satisfied",
        )
    }

    #[test]
    fn delete_clause_not_simplified() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -3, 4;
            ])
            .unwrap();

        let hashes = [
            checker.ctx.checker_state.clause_hash(&lits![1, 2, 3]),
            checker.ctx.checker_state.clause_hash(&lits![-3, 4]),
        ];

        checker
            .self_check_step(ProofStep::AtClause {
                redundant: false,
                clause: &lits![1, 2, 4],
                propagation_hashes: &hashes[..],
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteClause {
                clause: &lits![1, 2, 3],
                proof: DeleteClauseProof::Simplified,
            }),
            "not subsumed",
        )
    }

    #[test]
    fn model_unit_conflict() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1;
                2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::Model {
                assignment: &lits![-1, 2, -3],
            }),
            "conflicts with unit clause",
        )
    }

    #[test]
    fn model_internal_conflict() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                2, 3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::Model {
                assignment: &lits![-1, 1, 2, -3],
            }),
            "conflicting assignment",
        )
    }

    #[test]
    fn model_clause_unsat() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2, 3;
                -1, -2, 3;
                1, -2, -3;
            ])
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::Model {
                assignment: &lits![-1, 2, 3],
            }),
            "does not satisfy clause",
        )
    }
    #[test]
    fn model_conflicts_assumptions() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2;
                -1, 2;
            ])
            .unwrap();

        checker
            .self_check_step(ProofStep::Assumptions {
                assumptions: &lits![-2],
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::Model {
                assignment: &lits![1, 2],
            }),
            "does not contain assumption",
        )
    }

    #[test]
    fn model_misses_assumption() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2;
                -1, 2;
            ])
            .unwrap();

        checker
            .self_check_step(ProofStep::Assumptions {
                assumptions: &lits![-3],
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::Model {
                assignment: &lits![1, 2],
            }),
            "does not contain assumption",
        )
    }

    #[test]
    fn failed_core_with_non_assumed_vars() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2;
                -1, 2;
            ])
            .unwrap();

        checker
            .self_check_step(ProofStep::Assumptions {
                assumptions: &lits![-2],
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::FailedAssumptions {
                failed_core: &lits![-2, -3],
                propagation_hashes: &[],
            }),
            "contains non-assumed variables",
        )
    }

    #[test]
    fn failed_assumptions_with_missing_propagations() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2;
                -1, 2;
                -3, -2;
            ])
            .unwrap();

        checker
            .self_check_step(ProofStep::Assumptions {
                assumptions: &lits![3],
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::FailedAssumptions {
                failed_core: &lits![3],
                propagation_hashes: &[],
            }),
            "AT check failed",
        )
    }

    #[test]
    fn failed_assumptions_with_conflicting_assumptions() {
        let mut checker = Checker::new();
        checker
            .add_formula(&cnf_formula![
                1, 2;
                -1, 2;
                -3, -2;
            ])
            .unwrap();

        checker
            .self_check_step(ProofStep::Assumptions {
                assumptions: &lits![3, -3, 4],
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::FailedAssumptions {
                failed_core: &lits![3, -3],
                propagation_hashes: &[],
            })
            .unwrap();
    }

    #[test]
    fn add_clause_to_non_sampling_var() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::ChangeSamplingMode {
                var: Var::from_dimacs(1),
                sample: false,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::AddClause {
                clause: &lits![1, 2, 3],
            }),
            "not a sampling variable",
        )
    }

    #[test]
    fn add_clause_to_hidden_var() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: None,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::AddClause {
                clause: &lits![1, 2, 3],
            }),
            "not a sampling variable",
        )
    }

    #[test]
    fn colloding_user_vars() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(2),
                user: Some(Var::from_dimacs(1)),
            }),
            "used for two different variables",
        )
    }

    #[test]
    fn observe_without_setting_mode() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: None,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            }),
            "still hidden",
        )
    }

    #[test]
    fn hide_hidden_var() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: None,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: None,
            }),
            "no user name to remove",
        )
    }

    #[test]
    fn delete_user_var() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteVar {
                var: Var::from_dimacs(1),
            }),
            "corresponds to user variable",
        )
    }

    #[test]
    fn delete_in_use_var() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::AddClause {
                clause: &lits![1, 2, 3],
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: None,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::DeleteVar {
                var: Var::from_dimacs(1),
            }),
            "still has clauses",
        )
    }

    #[test]
    fn invalid_hidden_to_sample() {
        let mut checker = Checker::new();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: Some(Var::from_dimacs(1)),
            })
            .unwrap();

        checker
            .self_check_step(ProofStep::UserVarName {
                global: Var::from_dimacs(1),
                user: None,
            })
            .unwrap();

        expect_check_failed(
            checker.self_check_step(ProofStep::ChangeSamplingMode {
                var: Var::from_dimacs(1),
                sample: true,
            }),
            "cannot sample hidden variable",
        )
    }
}
