use varisat::checker::{CheckedProofStep, ProofProcessor};

use failure::Error;

/// Prints a simple transcript of the proof.
///
/// This shows whether the formula was proven unsatisfiable or whether a model is found. It also
#[derive(Default)]
pub struct Transcript {
    new_clauses: usize,
}

impl Transcript {
    /// Print how many new claues were loaded since the last transcript line
    fn print_loaded_clauses(&mut self) {
        if self.new_clauses > 0 {
            println!("t LOADED {} CLAUSES", self.new_clauses);
            self.new_clauses = 0;
        }
    }
}

impl ProofProcessor for Transcript {
    fn process_step(&mut self, step: &CheckedProofStep) -> Result<(), Error> {
        match &step {
            CheckedProofStep::AddClause { .. } | CheckedProofStep::DuplicatedClause { .. } => {
                self.new_clauses += 1;
                return Ok(());
            }
            _ => (),
        }
        match step {
            CheckedProofStep::AtClause { clause, .. } => {
                if clause.is_empty() {
                    self.print_loaded_clauses();
                    println!("t UNSAT");
                }
            }
            CheckedProofStep::Assumptions { assumptions } => {
                self.print_loaded_clauses();
                println!("t ASSUME {} LITERALS", assumptions.len());
            }
            CheckedProofStep::FailedAssumptions { failed_core, .. } => {
                self.print_loaded_clauses();
                println!("t UNSAT WITH {} ASSUMPTIONS", failed_core.len());
            }
            CheckedProofStep::Model { .. } => {
                self.print_loaded_clauses();
                println!("t SAT");
            }
            _ => (),
        }
        Ok(())
    }
}
