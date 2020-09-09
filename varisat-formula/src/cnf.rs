//! CNF formulas.
use std::cmp::max;
use std::fmt;
use std::ops::Range;

use crate::lit::{Lit, Var};

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

    /// Whether the set of clauses is empty.
    pub fn is_empty(&self) -> bool {
        self.clause_ranges.is_empty()
    }

    /// Iterator over all clauses.
    pub fn iter(&self) -> impl Iterator<Item = &[Lit]> {
        let literals = &self.literals;
        self.clause_ranges
            .iter()
            .map(move |range| &literals[range.clone()])
    }
}

/// Convert an iterable of [`Lit`] slices into a CnfFormula
impl<Clauses, Item> From<Clauses> for CnfFormula
where
    Clauses: IntoIterator<Item = Item>,
    Item: std::borrow::Borrow<[Lit]>,
{
    fn from(clauses: Clauses) -> CnfFormula {
        let mut cnf_formula = CnfFormula::new();
        for clause in clauses {
            cnf_formula.add_clause(clause.borrow());
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

/// Extend a formula with new variables and clauses.
pub trait ExtendFormula: Sized {
    /// Appends a clause to the formula.
    fn add_clause(&mut self, literals: &[Lit]);

    /// Add a new variable to the formula and return it.
    fn new_var(&mut self) -> Var;

    /// Add a new variable to the formula and return it as positive literal.
    fn new_lit(&mut self) -> Lit {
        self.new_var().positive()
    }

    /// Iterator over multiple new variables.
    fn new_var_iter(&mut self, count: usize) -> NewVarIter<Self> {
        NewVarIter {
            formula: self,
            vars_left: count,
            phantom: std::marker::PhantomData,
        }
    }

    /// Iterator over multiple new literals.
    fn new_lit_iter(&mut self, count: usize) -> NewVarIter<Self, Lit> {
        NewVarIter {
            formula: self,
            vars_left: count,
            phantom: std::marker::PhantomData,
        }
    }

    /// Add multiple new variables and return them.
    ///
    /// Returns a uniform tuple of variables. The number of variables is inferred, so it can be used
    /// like `let (x, y, z) = formula.new_vars()`.
    fn new_vars<Vars: UniformTuple<Var>>(&mut self) -> Vars {
        Vars::tuple_from_iter(self.new_var_iter(Vars::tuple_len()))
    }

    /// Add multiple new variables and return them as positive literals.
    ///
    /// Returns a uniform tuple of variables. The number of variables is inferred, so it can be used
    /// like `let (x, y, z) = formula.new_lits()`.
    fn new_lits<Lits: UniformTuple<Lit>>(&mut self) -> Lits {
        Lits::tuple_from_iter(self.new_lit_iter(Lits::tuple_len()))
    }
}

/// Iterator over new variables or literals.
///
/// Created by the [`new_var_iter`][ExtendFormula::new_var_iter] and
/// [`new_lit_iter`][ExtendFormula::new_lit_iter] methods of [`ExtendFormula`].
pub struct NewVarIter<'a, F, V = Var> {
    formula: &'a mut F,
    vars_left: usize,
    phantom: std::marker::PhantomData<V>,
}

impl<'a, F, V> Iterator for NewVarIter<'a, F, V>
where
    F: ExtendFormula,
    V: From<Var>,
{
    type Item = V;

    fn next(&mut self) -> Option<V> {
        if self.vars_left == 0 {
            None
        } else {
            let var = self.formula.new_var();
            self.vars_left -= 1;
            Some(V::from(var))
        }
    }
}

impl ExtendFormula for CnfFormula {
    fn add_clause(&mut self, clause: &[Lit]) {
        let begin = self.literals.len();
        self.literals.extend_from_slice(clause);
        let end = self.literals.len();

        for &lit in self.literals[begin..end].iter() {
            self.var_count = max(lit.index() + 1, self.var_count);
        }

        self.clause_ranges.push(begin..end);
    }

    fn new_var(&mut self) -> Var {
        let var = Var::from_index(self.var_count);
        self.var_count += 1;
        var
    }
}

/// Helper trait to initialize multiple variables of the same type.
pub trait UniformTuple<Item> {
    fn tuple_len() -> usize;
    fn tuple_from_iter(items: impl Iterator<Item = Item>) -> Self;
}

macro_rules! ignore_first {
    ($a:tt, $b:tt) => {
        $b
    };
}

macro_rules! array_like_impl {
    ($count:expr, $($call:tt)*) => {
        impl<Item> UniformTuple<Item> for ($(ignore_first!($call, Item)),*) {
            fn tuple_len() -> usize { $count }
            fn tuple_from_iter(mut items: impl Iterator<Item = Item>) -> Self {
                ($(items.next().unwrap().into $call),*)
            }
        }
    }
}

macro_rules! array_like_impl_4 {
    ($count:expr, $($call:tt)*) => {
        array_like_impl!($count * 4 + 2, $(()()()$call)* ()());
        array_like_impl!($count * 4 + 3, $(()()()$call)* ()()());
        array_like_impl!($count * 4 + 4, $(()()()$call)* ()()()());
        array_like_impl!($count * 4 + 5, $(()()()$call)* ()()()()());
    }
}

array_like_impl_4!(0,);
array_like_impl_4!(1, ());
array_like_impl_4!(2, ()());
array_like_impl_4!(3, ()()());
array_like_impl_4!(4, ()()()());

#[cfg(any(test, feature = "proptest-strategies"))]
#[doc(hidden)]
pub mod strategy {
    use super::*;

    use proptest::{collection::SizeRange, prelude::*, *};

    use crate::lit::strategy::lit;

    pub fn vec_formula(
        vars: impl Strategy<Value = usize>,
        clauses: impl Into<SizeRange>,
        clause_len: impl Into<SizeRange>,
    ) -> impl Strategy<Value = Vec<Vec<Lit>>> {
        let clauses = clauses.into();
        let clause_len = clause_len.into();

        // Not using ind_flat_map makes shrinking too expensive
        vars.prop_ind_flat_map(move |vars| {
            collection::vec(
                collection::vec(lit(0..vars), clause_len.clone()),
                clauses.clone(),
            )
        })
    }

    pub fn cnf_formula(
        vars: impl Strategy<Value = usize>,
        clauses: impl Into<SizeRange>,
        clause_len: impl Into<SizeRange>,
    ) -> impl Strategy<Value = CnfFormula> {
        let clauses = clauses.into();
        let clause_len = clause_len.into();

        let clause_lens = collection::vec(collection::vec(Just(()), clause_len), clauses);
        (vars, clause_lens).prop_flat_map(move |(vars, clause_lens)| {
            let total_lits: usize = clause_lens.iter().map(|l| l.len()).sum();
            collection::vec(lit(0..vars), total_lits)
                .prop_map(move |literals| {
                    let mut clause_ranges = Vec::with_capacity(clause_lens.len());

                    let mut offset = 0;
                    for len in clause_lens.iter() {
                        clause_ranges.push(offset..offset + len.len());
                        offset += len.len();
                    }

                    CnfFormula {
                        var_count: vars,
                        literals,
                        clause_ranges,
                    }
                })
                .no_shrink() // Shrinking too expensive without this
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{strategy::*, *};

    use proptest::*;

    #[test]
    fn new_vars() {
        let mut formula = CnfFormula::new();
        let (x, y, z) = formula.new_vars();

        assert_ne!(x, y);
        assert_ne!(y, z);
        assert_ne!(x, y);
        assert_eq!(formula.var_count(), 3);
    }

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

    proptest! {
        #[test]
        fn roundtrip_from_vec(input in vec_formula(1..200usize, 0..1000, 0..10)) {
            let formula = CnfFormula::from(input.clone());

            for (clause, ref_clause) in formula.iter().zip(input.iter()) {
                prop_assert_eq!(clause, &ref_clause[..]);
            }

            let var_count = input
                .iter()
                .flat_map(|clause| clause.iter().map(|lit| lit.index() + 1))
                .max()
                .unwrap_or(0);

            prop_assert_eq!(formula.var_count(), var_count);
        }

        #[test]
        fn roundtrip_from_cnf(input in cnf_formula(1..100usize, 0..1000, 0..10)) {
            let roundtrip = CnfFormula::from(input.iter());

            for (clause_a, clause_b) in input.iter().zip(roundtrip.iter()) {
                prop_assert_eq!(clause_a, clause_b);
            }

            prop_assert!(roundtrip.var_count() <= input.var_count());

            if roundtrip.var_count() == input.var_count() {
                prop_assert_eq!(roundtrip, input);
            }
        }
    }
}
