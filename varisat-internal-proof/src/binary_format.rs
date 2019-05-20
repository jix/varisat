//! Binary format for varisat proofs.
use std::io::{self, BufRead, Write};

use failure::Error;

use varisat_formula::{Lit, Var};

use crate::vli_enc::{read_u64, write_u64};

use super::{ClauseHash, DeleteClauseProof, ProofStep};

macro_rules! step_codes {
    ($counter:expr, $name:ident, ) => {
        const $name: u64 = $counter;
    };
    ($counter:expr, $name:ident, $($names:ident),* ,) => {
        const $name: u64 = $counter;
        step_codes!($counter + 1, $($names),* ,);
    };
}

step_codes!(
    0,
    CODE_SOLVER_VAR_NAMES,
    CODE_AT_CLAUSE_RED,
    CODE_AT_CLAUSE_IRRED,
    CODE_UNIT_CLAUSES,
    CODE_DELETE_CLAUSE_REDUNDANT,
    CODE_DELETE_CLAUSE_SIMPLIFIED,
    CODE_DELETE_CLAUSE_SATISFIED,
    CODE_CHANGE_HASH_BITS,
    CODE_MODEL,
    CODE_ADD_CLAUSE,
    CODE_ASSUMPTIONS,
    CODE_FAILED_ASSUMPTIONS,
);

// Using a random value here makes it unlikely that a corrupted proof will be silently truncated and
// accepted
const CODE_END: u64 = 0x9ac3391f4294c211;

/// Writes a proof step in the varisat format
pub fn write_step<'s>(target: &mut impl Write, step: &'s ProofStep<'s>) -> io::Result<()> {
    match *step {
        ProofStep::SolverVarNames { update } => {
            write_u64(&mut *target, CODE_SOLVER_VAR_NAMES)?;
            write_variable_updates(&mut *target, update)?;
        }

        ProofStep::AddClause { clause } => {
            write_u64(&mut *target, CODE_ADD_CLAUSE)?;
            write_literals(&mut *target, clause)?;
        }

        ProofStep::AtClause {
            redundant,
            clause,
            propagation_hashes,
        } => {
            if redundant {
                write_u64(&mut *target, CODE_AT_CLAUSE_RED)?;
            } else {
                write_u64(&mut *target, CODE_AT_CLAUSE_IRRED)?;
            }
            write_literals(&mut *target, clause)?;
            write_hashes(&mut *target, propagation_hashes)?;
        }

        ProofStep::UnitClauses(units) => {
            write_u64(&mut *target, CODE_UNIT_CLAUSES)?;
            write_unit_clauses(&mut *target, units)?;
        }

        ProofStep::DeleteClause { clause, proof } => {
            match proof {
                DeleteClauseProof::Redundant => {
                    write_u64(&mut *target, CODE_DELETE_CLAUSE_REDUNDANT)?;
                }
                DeleteClauseProof::Simplified => {
                    write_u64(&mut *target, CODE_DELETE_CLAUSE_SIMPLIFIED)?;
                }
                DeleteClauseProof::Satisfied => {
                    write_u64(&mut *target, CODE_DELETE_CLAUSE_SATISFIED)?;
                }
            }

            write_literals(&mut *target, clause)?;
        }

        ProofStep::ChangeHashBits(bits) => {
            write_u64(&mut *target, CODE_CHANGE_HASH_BITS)?;
            write_u64(&mut *target, bits as u64)?;
        }

        ProofStep::Model(model) => {
            write_u64(&mut *target, CODE_MODEL)?;
            write_literals(&mut *target, model)?;
        }

        ProofStep::Assumptions(assumptions) => {
            write_u64(&mut *target, CODE_ASSUMPTIONS)?;
            write_literals(&mut *target, assumptions)?;
        }

        ProofStep::FailedAssumptions {
            failed_core,
            propagation_hashes,
        } => {
            write_u64(&mut *target, CODE_FAILED_ASSUMPTIONS)?;
            write_literals(&mut *target, failed_core)?;
            write_hashes(&mut *target, propagation_hashes)?;
        }

        ProofStep::End => {
            write_u64(&mut *target, CODE_END)?;
        }
    }

    Ok(())
}

#[derive(Default)]
pub struct Parser {
    lit_buf: Vec<Lit>,
    var_update_buf: Vec<(Var, Option<Var>)>,
    hash_buf: Vec<ClauseHash>,
    unit_buf: Vec<(Lit, ClauseHash)>,
}

impl Parser {
    pub fn parse_step<'a>(&'a mut self, source: &mut impl BufRead) -> Result<ProofStep<'a>, Error> {
        let code = read_u64(&mut *source)?;
        match code {
            CODE_SOLVER_VAR_NAMES => {
                read_variable_updates(&mut *source, &mut self.var_update_buf)?;
                Ok(ProofStep::SolverVarNames {
                    update: &self.var_update_buf,
                })
            }
            CODE_ADD_CLAUSE => {
                read_literals(&mut *source, &mut self.lit_buf)?;
                Ok(ProofStep::AddClause {
                    clause: &self.lit_buf,
                })
            }
            CODE_AT_CLAUSE_IRRED | CODE_AT_CLAUSE_RED => {
                read_literals(&mut *source, &mut self.lit_buf)?;
                read_hashes(&mut *source, &mut self.hash_buf)?;
                Ok(ProofStep::AtClause {
                    redundant: code == CODE_AT_CLAUSE_RED,
                    clause: &self.lit_buf,
                    propagation_hashes: &self.hash_buf,
                })
            }
            CODE_UNIT_CLAUSES => {
                read_unit_clauses(&mut *source, &mut self.unit_buf)?;
                Ok(ProofStep::UnitClauses(&self.unit_buf))
            }
            CODE_DELETE_CLAUSE_REDUNDANT
            | CODE_DELETE_CLAUSE_SIMPLIFIED
            | CODE_DELETE_CLAUSE_SATISFIED => {
                let proof = match code {
                    CODE_DELETE_CLAUSE_REDUNDANT => DeleteClauseProof::Redundant,
                    CODE_DELETE_CLAUSE_SIMPLIFIED => DeleteClauseProof::Simplified,
                    CODE_DELETE_CLAUSE_SATISFIED => DeleteClauseProof::Satisfied,
                    _ => unreachable!(),
                };
                read_literals(&mut *source, &mut self.lit_buf)?;
                Ok(ProofStep::DeleteClause {
                    clause: &self.lit_buf,
                    proof,
                })
            }
            CODE_CHANGE_HASH_BITS => {
                let bits = read_u64(&mut *source)? as u32;
                Ok(ProofStep::ChangeHashBits(bits))
            }
            CODE_MODEL => {
                read_literals(&mut *source, &mut self.lit_buf)?;
                Ok(ProofStep::Model(&self.lit_buf))
            }
            CODE_ASSUMPTIONS => {
                read_literals(&mut *source, &mut self.lit_buf)?;
                Ok(ProofStep::Assumptions(&self.lit_buf))
            }
            CODE_FAILED_ASSUMPTIONS => {
                read_literals(&mut *source, &mut self.lit_buf)?;
                read_hashes(&mut *source, &mut self.hash_buf)?;
                Ok(ProofStep::FailedAssumptions {
                    failed_core: &self.lit_buf,
                    propagation_hashes: &self.hash_buf,
                })
            }
            CODE_END => Ok(ProofStep::End),
            _ => failure::bail!("parse error"),
        }
    }
}

/// Writes a slice of variable updates for a varisat proof
fn write_variable_updates(
    target: &mut impl Write,
    updates: &[(Var, Option<Var>)],
) -> io::Result<()> {
    write_u64(&mut *target, updates.len() as u64)?;
    for &update in updates {
        write_u64(&mut *target, update.0.index() as u64)?;
        write_u64(
            &mut *target,
            update.1.map(|var| var.index() as u64 + 1).unwrap_or(0),
        )?;
    }
    Ok(())
}

/// Read a slice of variable updates from a varisat proof
fn read_variable_updates(
    source: &mut impl BufRead,
    updates: &mut Vec<(Var, Option<Var>)>,
) -> Result<(), io::Error> {
    updates.clear();
    let len = read_u64(&mut *source)? as usize;
    updates.reserve(len);
    for _ in 0..len {
        let var_0 = Var::from_index(read_u64(&mut *source)? as usize);
        let var_1 = match read_u64(&mut *source)? {
            0 => None,
            x => Some(Var::from_index(x as usize - 1)),
        };
        updates.push((var_0, var_1));
    }
    Ok(())
}

/// Writes a slice of literals for a varisat proof
fn write_literals(target: &mut impl Write, literals: &[Lit]) -> io::Result<()> {
    write_u64(&mut *target, literals.len() as u64)?;
    for &lit in literals {
        write_u64(&mut *target, lit.code() as u64)?;
    }
    Ok(())
}

/// Read a slice of literals from a varisat proof
fn read_literals(source: &mut impl BufRead, literals: &mut Vec<Lit>) -> Result<(), io::Error> {
    literals.clear();
    let len = read_u64(&mut *source)? as usize;
    literals.reserve(len);
    for _ in 0..len {
        literals.push(Lit::from_code(read_u64(&mut *source)? as usize));
    }
    Ok(())
}

/// Writes a slice of clause hashes for a varisat proof
fn write_hashes(target: &mut impl Write, hashes: &[ClauseHash]) -> io::Result<()> {
    write_u64(&mut *target, hashes.len() as u64)?;
    for &hash in hashes {
        write_u64(&mut *target, hash as u64)?;
    }
    Ok(())
}

/// Read a slice of clause hashes from a varisat proof
fn read_hashes(source: &mut impl BufRead, hashes: &mut Vec<ClauseHash>) -> Result<(), io::Error> {
    hashes.clear();
    let len = read_u64(&mut *source)? as usize;
    hashes.reserve(len);
    for _ in 0..len {
        hashes.push(read_u64(&mut *source)? as ClauseHash);
    }
    Ok(())
}

/// Writes a slice of unit clauses for a varisat proof
fn write_unit_clauses(target: &mut impl Write, units: &[(Lit, ClauseHash)]) -> io::Result<()> {
    write_u64(&mut *target, units.len() as u64)?;
    for &(lit, hash) in units {
        write_u64(&mut *target, lit.code() as u64)?;
        write_u64(&mut *target, hash as u64)?;
    }
    Ok(())
}

/// Read a slice of unit clauses from a varisat proof
fn read_unit_clauses(
    source: &mut impl BufRead,
    units: &mut Vec<(Lit, ClauseHash)>,
) -> Result<(), io::Error> {
    units.clear();
    let len = read_u64(&mut *source)? as usize;
    units.reserve(len);
    for _ in 0..len {
        let lit = Lit::from_code(read_u64(&mut *source)? as usize);
        let hash = read_u64(&mut *source)? as ClauseHash;
        units.push((lit, hash));
    }
    Ok(())
}
