//! CNF formulas.
use std::cmp::max;
use std::fmt;
use std::iter::Extend;
use std::ops::Range;

use crate::lit::Lit;

/// A formula in conjunctive normal form (CNF).
///
/// Equivalent to Vec<Vec<Lit>> but more efficient as it uses a single buffer for all literals.
#[derive(Default, Eq)]
pub struct CnfFormula {
    var_count: usize,
    literals: Vec<Lit>,
    clause_ranges: Vec<Range<usize>>,
}

impl CnfFormula {
    /// Create an empty CNF formula.
    pub fn new() -> CnfFormula {
        CnfFormula::default()
    }

    /// Number of variables in the formula.
    ///
    /// This also counts missing variables if a variable with a higher index is present.
    /// A vector of this length can be indexed with the variable indices present.
    pub fn var_count(&self) -> usize {
        self.var_count
    }

    /// Increase the number of variables in the formula.
    ///
    /// If the parameter is less than the current variable count do nothing.
    pub fn set_var_count(&mut self, count: usize) {
        self.var_count = max(self.var_count, count)
    }

    /// Number of clauses in the formula.
    pub fn len(&self) -> usize {
        self.clause_ranges.len()
    }

    /// Appends a clause to the formula.
    ///
    /// `literals` can be an `IntoIterator<Item = Lit>` or `IntoIterator<Item = &Lit>`.
    pub fn add_clause<L>(&mut self, literals: impl IntoIterator<Item = L>)
    where
        Vec<Lit>: Extend<L>,
    {
        let begin = self.literals.len();
        self.literals.extend(literals);
        let end = self.literals.len();

        for &lit in self.literals[begin..end].iter() {
            self.var_count = max(lit.index() + 1, self.var_count);
        }

        self.clause_ranges.push(begin..end);
    }

    /// Iterator over all clauses.
    pub fn iter(&self) -> impl Iterator<Item = &[Lit]> {
        let literals = &self.literals;
        self.clause_ranges
            .iter()
            .map(move |range| &literals[range.clone()])
    }
}

/// Convert any iterable of [`Lit`] iterables into a CnfFormula
impl<F, I, L> From<F> for CnfFormula
where
    F: IntoIterator<Item = I>,
    I: IntoIterator<Item = L>,
    Vec<Lit>: Extend<L>,
{
    fn from(formula: F) -> CnfFormula {
        let mut cnf_formula = CnfFormula::new();
        for clause in formula {
            cnf_formula.add_clause(clause);
        }
        cnf_formula
    }
}

impl fmt::Debug for CnfFormula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.var_count(), f)?;
        f.debug_list().entries(self.iter()).finish()
    }
}

impl PartialEq for CnfFormula {
    fn eq(&self, other: &CnfFormula) -> bool {
        self.var_count() == other.var_count()
            && self.clause_ranges.len() == other.clause_ranges.len()
            && self
                .clause_ranges
                .iter()
                .zip(other.clause_ranges.iter())
                .all(|(range_a, range_b)| {
                    self.literals[range_a.clone()] == other.literals[range_b.clone()]
                })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_roundtrip() {
        let input = cnf![
            1, 2, 3;
            -1, -2;
            7, 2;
            ;
            4, 5;
        ];

        let formula = CnfFormula::from(input.iter().cloned());

        for (clause, &ref_clause) in formula.iter().zip(input.iter()) {
            assert_eq!(clause, ref_clause);
        }

        assert_eq!(formula.var_count(), 7);
    }
}
