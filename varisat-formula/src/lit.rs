//! Literals and variables.
use std::{fmt, ops};

/// The backing type used to represent literals and variables.
pub type LitIdx = u32;

/// A boolean variable.
///
/// A boolean value is represented by an index. Internally these are 0-based, i.e. the first
/// variable has the index 0. For user IO a 1-based index is used, to allow denoting negated
/// variables using negative integers. This convention is also used in the DIMACS CNF format.
///
/// Creating a variable with an index larger than `Var::max_var().index()` is unsupported. This
/// might panic or be interpreted as a different variable.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Var {
    index: LitIdx,
}

impl Var {
    /// Creates a variable from a 1-based index as used in the DIMCAS CNF encoding.
    ///
    /// The parameter must be positive and may not represent a variable past `Var::max_var()`.
    #[inline]
    pub fn from_dimacs(number: isize) -> Var {
        debug_assert!(number > 0);
        Var::from_index((number - 1) as usize)
    }

    /// Creates a variable from a 0-based index.
    ///
    /// The index may not represent a variable past `Var::max_var()`.
    #[inline]
    pub fn from_index(index: usize) -> Var {
        debug_assert!(index <= Var::max_var().index());
        Var {
            index: index as LitIdx,
        }
    }

    /// The 1-based index representing this variable in the DIMACS CNF encoding.
    #[inline]
    pub fn to_dimacs(self) -> isize {
        (self.index + 1) as isize
    }

    /// The 0-based index representing this variable.
    #[inline]
    pub const fn index(self) -> usize {
        self.index as usize
    }

    /// The variable with largest index that is supported.
    ///
    /// This is less than the backing integer type supports. This enables storing a variable index
    /// and additional bits (as in `Lit`) or sentinel values in a single word.
    pub const fn max_var() -> Var {
        // Allow for sign or tag bits
        Var {
            index: LitIdx::max_value() >> 4,
        }
    }

    /// Largest number of variables supported.
    ///
    /// This is exactly `Var::max_var().index() + 1`.
    pub const fn max_count() -> usize {
        Self::max_var().index() + 1
    }

    /// Creates a literal from this var and a `bool` that is `true` when the literal is positive.
    ///
    /// Shortcut for `Lit::from_var(var, polarity)`.
    #[inline]
    pub fn lit(self, polarity: bool) -> Lit {
        Lit::from_var(self, polarity)
    }

    /// Creates a positive literal from this var.
    ///
    /// Shortcut for `Lit::positive(var)`.
    #[inline]
    pub fn positive(self) -> Lit {
        Lit::positive(self)
    }

    /// Creates a negative literal from this var.
    ///
    /// Shortcut for `Lit::negative(var)`.
    #[inline]
    pub fn negative(self) -> Lit {
        Lit::negative(self)
    }
}

/// Uses the 1-based DIMACS CNF encoding.
impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

/// Uses the 1-based DIMACS CNF encoding.
impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// A boolean literal.
///
/// A literal is a variable or the negation of a variable.
///
/// Conceptually a literal consists of a `Var` and a `bool` indicating whether the literal
/// represents the variable (positive literal) or its negation (negative literal).
///
/// Internally a literal is represented as an integer that is two times the index of its variable
/// when it is positive or one more when it is negative. This integer is called the `code` of the
/// literal.
///
/// The restriction on the range of allowed indices for `Var` also applies to `Lit`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Lit {
    code: LitIdx,
}

impl Lit {
    /// Creates a literal from a `Var` and a `bool` that is `true` when the literal is positive.
    #[inline]
    pub fn from_var(var: Var, polarity: bool) -> Lit {
        Lit::from_litidx(var.index, polarity)
    }

    /// Create a positive literal from a `Var`.
    #[inline]
    pub fn positive(var: Var) -> Lit {
        Lit::from_var(var, true)
    }

    /// Create a negative literal from a `Var`.
    #[inline]
    pub fn negative(var: Var) -> Lit {
        Lit::from_var(var, false)
    }

    /// Create a literal from a variable index and a `bool` that is `true` when the literal is
    /// positive.
    #[inline]
    pub fn from_index(index: usize, polarity: bool) -> Lit {
        Lit::from_var(Var::from_index(index), polarity)
    }

    /// Create a literal with the given encoding.
    #[inline]
    pub fn from_code(code: usize) -> Lit {
        debug_assert!(code <= Var::max_var().index() * 2 + 1);
        Lit {
            code: code as LitIdx,
        }
    }

    #[inline]
    fn from_litidx(index: LitIdx, polarity: bool) -> Lit {
        debug_assert!(index <= Var::max_var().index);
        Lit {
            code: (index << 1) | (!polarity as LitIdx),
        }
    }

    /// Creates a literal from an integer.
    ///
    /// The absolute value is used as 1-based index, the sign of
    /// the integer is used as sign of the literal.
    #[inline]
    pub fn from_dimacs(number: isize) -> Lit {
        Lit::from_var(Var::from_dimacs(number.abs()), number > 0)
    }

    /// 1-based Integer representation of the literal, opposite of `from_dimacs`.
    #[inline]
    pub fn to_dimacs(self) -> isize {
        let mut number = self.var().to_dimacs();
        if self.is_negative() {
            number = -number
        }
        number
    }

    /// 0-based index of the literal's _variable_.
    #[inline]
    pub fn index(self) -> usize {
        (self.code >> 1) as usize
    }

    /// The literal's variable.
    #[inline]
    pub fn var(self) -> Var {
        Var {
            index: self.code >> 1,
        }
    }

    /// Whether the literal is negative, i.e. a negated variable.
    #[inline]
    pub fn is_negative(self) -> bool {
        (self.code & 1) != 0
    }

    /// Whether the literal is positive, i.e. a non-negated variable.
    #[inline]
    pub fn is_positive(self) -> bool {
        !self.is_negative()
    }

    /// Two times the variable's index for positive literals and one more for negative literals.
    ///
    /// This is also the internal encoding.
    #[inline]
    pub fn code(self) -> usize {
        self.code as usize
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit {
            code: self.code ^ 1,
        }
    }
}

impl ops::BitXor<bool> for Lit {
    type Output = Lit;

    #[inline]
    fn bitxor(self, rhs: bool) -> Lit {
        Lit {
            code: self.code ^ (rhs as LitIdx),
        }
    }
}

impl From<Var> for Lit {
    #[inline]
    fn from(var: Var) -> Lit {
        Lit::positive(var)
    }
}

/// Uses the 1-based DIMACS CNF encoding.
impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

/// Uses the 1-based DIMACS CNF encoding.
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

#[cfg(any(test, feature = "proptest-strategies"))]
#[doc(hidden)]
pub mod strategy {
    use super::*;
    use proptest::{prelude::*, *};

    pub fn var(index: impl Strategy<Value = usize>) -> impl Strategy<Value = Var> {
        index.prop_map(|index| Var::from_index(index))
    }

    pub fn lit(index: impl Strategy<Value = usize>) -> impl Strategy<Value = Lit> {
        (var(index), bool::ANY).prop_map(|(var, polarity)| var.lit(polarity))
    }
}
