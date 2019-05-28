//! Data associated with variables.

/// Variable sampling mode.
///
/// This partitions all variables into three sets. Using these partitions it is possible to specify
/// equivalence vs. equisatisfiability per variable. Let V be the set of all variables, S, W and H
/// the sets of Sampling, Witness and Hidden variables. Let F be the input formula and G be the
/// current formula. The following invariants are upheld:
///
///   * The formulas are always equisatisfiable:
///     (∃ V) G ⇔ (∃ V) F
///   * Restricted to the sampling variables they are equivalent:
///     (∀ S) ((∃ V∖S) G ⇔ (∃ V∖S) F)
///   * Restricted to the non-hidden variables the input formula is implied:
///     (∀ V∖H) ((∃ H) G ⇒ (∃ H) F)
///
/// This ensures that the solver will be able to find and extend each satisfiable assignment of the
/// sampling variables to an assignment that covers the witness variables.

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SamplingMode {
    Sample,
    Witness,
    Hide,
}

/// Data associated with variables.
///
/// This is available for each _global_ variable, even if eliminated within the solver.
#[derive(Clone)]
pub struct VarData {
    /// The variable's sampling mode.
    pub sampling_mode: SamplingMode,
    /// Whether the variable is forced by a unit clause.
    ///
    /// This is used to remember unit clauses after they are removed from the solver.
    pub unit: Option<bool>,
    /// True if there are no clauses containing this variable and other variables.
    ///
    /// This is the case if there are no clauses containing this variable or just a unit clause with
    /// this variable.
    pub isolated: bool,
    /// True if this variable is part of the current assumptions.
    pub assumed: bool,
    /// Whether the global variable was deleted.
    pub deleted: bool,
}

impl Default for VarData {
    fn default() -> VarData {
        VarData {
            sampling_mode: SamplingMode::Hide,
            unit: None,
            isolated: true,
            assumed: false,
            deleted: true,
        }
    }
}

impl VarData {
    /// Default variable data for a new user variable.
    pub fn user_default() -> VarData {
        VarData {
            sampling_mode: SamplingMode::Sample,
            deleted: false,
            ..VarData::default()
        }
    }
}
