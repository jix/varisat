//! Mappings between variable names

use varisat_formula::lit::LitIdx;
use varisat_formula::Var;

const NO_VAR_IDX: LitIdx = Var::max_count() as LitIdx;

/// A mapping from variables to variables.
#[derive(Default)]
pub struct VarMap {
    default_identity: bool,
    mapping: Vec<LitIdx>,
}

impl VarMap {
    /// Identity mapping over all variables.
    pub fn identity() -> VarMap {
        VarMap {
            default_identity: true,
            mapping: vec![],
        }
    }

    /// Look up a variable in the mapping
    pub fn get(&self, from: Var) -> Option<Var> {
        match self.mapping.get(from.index()).cloned() {
            Some(index) if index == NO_VAR_IDX => None,
            Some(index) => Some(Var::from_index(index as usize)),
            None if self.default_identity => Some(from),
            None => None,
        }
    }

    /// Insert a new mapping.
    ///
    /// Note that the parameters are reversed from the usual order, to match the naming convention
    /// used for maps.
    ///
    /// This has the precondition that `from` is not mapped.
    pub fn insert(&mut self, into: Var, from: Var) {
        self.ensure_mapping(from);
        debug_assert_eq!(self.mapping[from.index()], NO_VAR_IDX);
        self.mapping[from.index()] = into.index() as LitIdx
    }

    /// Remove a mapping.
    ///
    /// Does nothing if `from` is not mapped.
    pub fn remove(&mut self, from: Var) {
        self.ensure_mapping(from);
        self.mapping[from.index()] = NO_VAR_IDX;
    }

    /// Resize the internal mapping to cover `from`.
    fn ensure_mapping(&mut self, from: Var) {
        if self.mapping.len() <= from.index() {
            if self.default_identity {
                let range = (self.mapping.len() as LitIdx)..((from.index() + 1) as LitIdx);
                self.mapping.extend(range);
            } else {
                self.mapping.resize(from.index() + 1, NO_VAR_IDX);
            }
        }
    }
}

/// A bidirectional mapping between variables.
///
/// This is initialized with the identity mapping over all variables. It is possible to remove
/// variables from this mapping on both sides.
#[derive(Default)]
pub struct VarBiMap {
    fwd: VarMap,
    bwd: VarMap,
}

impl VarBiMap {
    /// Identity mapping over all variables.
    pub fn identity() -> VarBiMap {
        VarBiMap {
            fwd: VarMap::identity(),
            bwd: VarMap::identity(),
        }
    }

    /// Access the forward mapping.
    pub fn fwd(&self) -> &VarMap {
        &self.fwd
    }

    /// Access the backward mapping.
    pub fn bwd(&self) -> &VarMap {
        &self.bwd
    }

    /// Mutate the mapping in forward direction.
    pub fn fwd_mut(&mut self) -> VarBiMapMut {
        VarBiMapMut {
            fwd: &mut self.fwd,
            bwd: &mut self.bwd,
        }
    }

    /// Mutate the mapping in backward direction.
    pub fn bwd_mut(&mut self) -> VarBiMapMut {
        VarBiMapMut {
            fwd: &mut self.bwd,
            bwd: &mut self.fwd,
        }
    }
}

/// Mutable view of a [`VarBiMap`].
///
/// Helper so `VarBiMap` mutating routines can work in both directions.
pub struct VarBiMapMut<'a> {
    fwd: &'a mut VarMap,
    bwd: &'a mut VarMap,
}

impl<'a> VarBiMapMut<'a> {
    /// Insert a new mapping.
    ///
    /// Note that the parameters are reversed from the usual order, to match the naming convention
    /// used for maps.
    ///
    /// This has the precondition that `into` and `from` are not mapped.
    pub fn insert(&mut self, into: Var, from: Var) {
        self.fwd.insert(into, from);
        self.bwd.insert(from, into);
    }

    /// Remove a mapping.
    ///
    /// Does nothing if `from` is not mapped.
    pub fn remove(&mut self, from: Var) {
        if let Some(into) = self.fwd.get(from) {
            self.fwd.remove(from);
            self.bwd.remove(into);
        }
    }
}
