use std::io::{self, Write};

use varisat_formula::Lit;
use varisat_internal_proof::ProofStep;

/// Writes a proof step in DRAT format
pub fn write_step<'s>(target: &mut impl Write, step: &'s ProofStep<'s>) -> io::Result<()> {
    match step {
        ProofStep::AtClause { clause, .. } => {
            write_literals(target, &clause)?;
        }
        ProofStep::UnitClauses(units) => {
            for &(unit, _hash) in units.iter() {
                write_literals(target, &[unit])?;
            }
        }
        ProofStep::DeleteClause { clause, .. } => {
            target.write_all(b"d ")?;
            write_literals(target, &clause[..])?;
        }
        ProofStep::SolverVarName { .. }
        | ProofStep::UserVarName { .. }
        | ProofStep::DeleteVar { .. }
        | ProofStep::ChangeSamplingMode { .. }
        | ProofStep::ChangeHashBits(..)
        | ProofStep::Model(..)
        | ProofStep::End => (),
        ProofStep::AddClause { .. } => {
            // TODO allow error handling here?
            panic!("incremental clause additions not supported by DRAT proofs");
        }
        ProofStep::Assumptions(..) | ProofStep::FailedAssumptions { .. } => {
            // TODO allow error handling here?
            panic!("assumptions not supported by DRAT proofs");
        }
    }

    Ok(())
}

/// Writes a proof step in binary DRAT format
pub fn write_binary_step<'s>(target: &mut impl Write, step: &'s ProofStep<'s>) -> io::Result<()> {
    match step {
        ProofStep::AtClause { clause, .. } => {
            target.write_all(b"a")?;
            write_binary_literals(target, &clause)?;
        }
        ProofStep::UnitClauses(units) => {
            for &(unit, _hash) in units.iter() {
                target.write_all(b"a")?;
                write_binary_literals(target, &[unit])?;
            }
        }
        ProofStep::DeleteClause { clause, .. } => {
            target.write_all(b"d")?;
            write_binary_literals(target, &clause[..])?;
        }
        ProofStep::SolverVarName { .. }
        | ProofStep::UserVarName { .. }
        | ProofStep::DeleteVar { .. }
        | ProofStep::ChangeSamplingMode { .. }
        | ProofStep::ChangeHashBits(..)
        | ProofStep::Model(..)
        | ProofStep::End => (),
        ProofStep::AddClause { .. } => {
            // TODO allow error handling here?
            panic!("incremental clause additions not supported by DRAT proofs");
        }
        ProofStep::Assumptions(..) | ProofStep::FailedAssumptions { .. } => {
            // TODO allow error handling here?
            panic!("assumptions not supported by DRAT proofs");
        }
    }

    Ok(())
}

/// Writes the literals of a clause for a step in a DRAT proof.
fn write_literals(target: &mut impl Write, literals: &[Lit]) -> io::Result<()> {
    for &lit in literals {
        itoa::write(&mut *target, lit.to_dimacs())?;
        target.write_all(b" ")?;
    }
    target.write_all(b"0\n")?;
    Ok(())
}

/// Writes the literals of a clause for a step in a binary DRAT proof.
fn write_binary_literals(target: &mut impl Write, literals: &[Lit]) -> io::Result<()> {
    for &lit in literals {
        let drat_code = lit.code() as u64 + 2;
        leb128::write::unsigned(target, drat_code)?;
    }
    target.write_all(&[0])?;
    Ok(())
}
