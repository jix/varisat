//! Variable mapping and metadata.

use std::cmp::max;

use partial_ref::{partial, PartialRef};

use varisat_formula::{Lit, Var};
use varisat_internal_proof::ProofStep;

use crate::context::{parts::*, set_var_count, Context};
use crate::decision;
use crate::proof;

pub mod data;
pub mod var_map;

use data::{SamplingMode, VarData};
use var_map::{VarBiMap, VarBiMapMut, VarMap};

/// Variable mapping and metadata.
pub struct Variables {
    /// Bidirectional mapping from user variables to global variables.
    ///
    /// Initially this is the identity mapping. This ensures that in the non-incremental setting the
    /// map from used user variables to global variables is the identity. This is a requirement for
    /// generating proofs in non-native formats. Those proofs are not aware of variable renaming,
    /// but are restricted to the non-incremental setting, so this works out.
    ///
    /// This is also requried for native proofs, as they assume that the mapping during the initial
    /// load is the identity.
    global_from_user: VarBiMap,
    /// Bidirectional mapping from global variables to user variables.
    ///
    /// This starts with the empty mapping, so only used variables are allocated.
    solver_from_global: VarBiMap,
    /// User variables starting from this are unused so far.
    user_watermark: usize,
    /// User variables that were explicitly hidden by the user.
    user_freelist: Vec<Var>,
    /// Global variables starting from this may be remapped if a needed.
    global_watermark: usize,
    /// Global variables that can be recycled without increasing the global_watermark.
    global_freelist: Vec<Var>,
    /// Solver variables starting from this are unmapped.
    solver_watermark: usize,
    /// Solver variables that are unused and can be recycled.
    solver_freelist: Vec<Var>,

    /// Variable metadata.
    ///
    /// Indexed by global variable indices.
    var_data: Vec<VarData>,
}

impl Default for Variables {
    fn default() -> Variables {
        Variables {
            global_from_user: VarBiMap::identity(),
            solver_from_global: VarBiMap::default(),
            user_watermark: 0,
            user_freelist: vec![],
            global_watermark: 0,
            global_freelist: vec![],
            solver_watermark: 0,
            solver_freelist: vec![],

            var_data: vec![],
        }
    }
}

impl Variables {
    /// Number of allocated solver variables.
    pub fn solver_watermark(&self) -> usize {
        self.solver_watermark
    }

    /// Number of allocated global variables.
    pub fn global_watermark(&self) -> usize {
        self.global_watermark
    }

    /// Iterator over all user variables that are in use.
    pub fn user_var_iter<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        let global_from_user = self.global_from_user.fwd();
        (0..self.user_watermark)
            .map(|user_index| Var::from_index(user_index))
            .filter(move |&user_var| global_from_user.get(user_var).is_some())
    }

    /// Iterator over all global variables that are in use.
    pub fn global_var_iter<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        (0..self.global_watermark)
            .map(|global_index| Var::from_index(global_index))
            .filter(move |&global_var| !self.var_data[global_var.index()].deleted)
    }

    /// The user to global mapping.
    pub fn global_from_user(&self) -> &VarMap {
        &self.global_from_user.fwd()
    }

    /// The global to solver mapping.
    pub fn solver_from_global(&self) -> &VarMap {
        &self.solver_from_global.fwd()
    }

    /// The global to user mapping.
    pub fn user_from_global(&self) -> &VarMap {
        &self.global_from_user.bwd()
    }

    /// Mutable global to user mapping.
    pub fn user_from_global_mut(&mut self) -> VarBiMapMut {
        self.global_from_user.bwd_mut()
    }

    /// The solver to global mapping.
    pub fn global_from_solver(&self) -> &VarMap {
        &self.solver_from_global.bwd()
    }

    /// Mutable global to solver mapping.
    pub fn global_from_solver_mut(&mut self) -> VarBiMapMut {
        self.solver_from_global.bwd_mut()
    }

    /// Get an existing solver var for a user var.
    pub fn existing_solver_from_user(&self, user: Var) -> Var {
        let global = self
            .global_from_user()
            .get(user)
            .expect("no existing global var for user var");
        let solver = self
            .solver_from_global()
            .get(global)
            .expect("no existing solver var for global var");
        solver
    }

    /// Get an existing user var from a solver var.
    pub fn existing_user_from_solver(&self, solver: Var) -> Var {
        let global = self
            .global_from_solver()
            .get(solver)
            .expect("no existing global var for solver var");
        let user = self
            .user_from_global()
            .get(global)
            .expect("no existing user var for global var");
        user
    }

    /// Mutable reference to the var data for a solver variable.
    pub fn var_data_solver_mut(&mut self, solver: Var) -> &mut VarData {
        let global = self
            .global_from_solver()
            .get(solver)
            .expect("no existing global var for solver var");
        &mut self.var_data[global.index()]
    }

    /// Var data for a global variable.
    pub fn var_data_global(&self, global: Var) -> &VarData {
        &self.var_data[global.index()]
    }

    /// Check if a solver var is mapped to a global var
    pub fn solver_var_present(&self, solver: Var) -> bool {
        self.global_from_solver().get(solver).is_some()
    }
}

/// Maps a user variable into a global variable.
///
/// If no matching global variable exists (can only happen if the user previously hid the
/// variable) a new global variable is allocated.
pub fn global_from_user<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    user: Var,
) -> Var {
    let variables = ctx.part_mut(VariablesP);

    variables.user_watermark = max(variables.user_watermark, user.index() + 1);

    let mut new_mapping = false;

    let global = variables
        .global_from_user
        .fwd()
        .get(user)
        .unwrap_or_else(|| {
            // Try to recycle a global var, otherwise use the global watermark.
            let global = variables
                .global_freelist
                .pop()
                .unwrap_or(Var::from_index(variables.global_watermark));

            // We remove an existing mapping (no-op when we recycle a global var).
            let mut user_from_global = variables.global_from_user.bwd_mut();
            user_from_global.remove(global);

            // And add the new mapping.
            variables.global_from_user.fwd_mut().insert(global, user);
            new_mapping = true;

            if variables.var_data.len() > global.index() {
                variables.var_data[global.index()] = VarData::user_default();
            } // else resize below

            global
        });

    if variables.var_data.len() <= global.index() {
        variables
            .var_data
            .resize(global.index() + 1, VarData::user_default());
    }

    // Now we update the global watermark to make sure that this mapping is not remapped.
    variables.global_watermark = max(variables.global_watermark, global.index() + 1);

    if new_mapping {
        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::UserVarName {
                global,
                user: Some(user),
            },
        );
    }

    global
}

/// Maps a global variable to a solver variable.
///
/// If no matching solver variable exists a new one is allocated.
pub fn solver_from_global<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    global: Var,
) -> Var {
    let variables = ctx.part_mut(VariablesP);

    let mut new_solver_var = false;

    let solver = variables
        .solver_from_global
        .fwd()
        .get(global)
        .unwrap_or_else(|| {
            // Try to recycle a solver var, otherwise use the solver watermark.
            let solver = variables
                .solver_freelist
                .pop()
                .unwrap_or(Var::from_index(variables.solver_watermark));

            // Unlike for the global from user case, we start with an empty mapping, so there
            // cannot be an existing mapping.

            variables
                .solver_from_global
                .fwd_mut()
                .insert(solver, global);

            new_solver_var = true;

            solver
        });

    if new_solver_var {
        let new_watermark = solver.index() + 1;
        if new_watermark > variables.solver_watermark {
            variables.solver_watermark = new_watermark;
            set_var_count(ctx.borrow(), new_watermark);
        }

        initialize_solver_var(ctx.borrow(), solver, global);

        if ctx.part(ProofP).native_format() {
            proof::add_step(
                ctx.borrow(),
                false,
                &ProofStep::SolverVarName {
                    global,
                    solver: Some(solver),
                },
            );
        }
    }

    solver
}

/// Maps a user variable to a solver variable.
///
/// Allocates global and solver variables as requried.
pub fn solver_from_user<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    user: Var,
) -> Var {
    let global = global_from_user(ctx.borrow(), user);
    let solver = solver_from_global(ctx.borrow(), global);
    solver
}

/// Allocates a currently unused user variable.
///
/// This is either a user variable above any user variable used so far, or a user variable that was
/// previously hidden by the user.
pub fn new_user_var<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
) -> Var {
    let variables = ctx.part_mut(VariablesP);
    let user_var = variables.user_freelist.pop().unwrap_or_else(|| {
        let user_var = Var::from_index(variables.user_watermark);
        variables.user_watermark += 1;
        user_var
    });
    // This ensures we allocate a global mapping _now_. This is important for the invariants
    // described above (see the `global_from_user` field comment).
    global_from_user(ctx.borrow(), user_var);
    user_var
}

/// Maps a slice of user lits to solver lits using [`solver_from_user`].
pub fn solver_from_user_lits<'a>(
    mut ctx: partial!(
        Context<'a>,
        mut AnalyzeConflictP,
        mut AssignmentP,
        mut BinaryClausesP,
        mut ImplGraphP,
        mut ProofP<'a>,
        mut SolverStateP,
        mut TmpFlagsP,
        mut VariablesP,
        mut VsidsP,
        mut WatchlistsP,
    ),
    solver_lits: &mut Vec<Lit>,
    user_lits: &[Lit],
) {
    solver_lits.clear();
    solver_lits.extend(
        user_lits
            .iter()
            .map(|user_lit| user_lit.map_var(|user_var| solver_from_user(ctx.borrow(), user_var))),
    )
}

/// Changes the sampling mode of a global variable.
///
/// If the mode is changed to hidden, an existing user mapping is automatically removed.
pub fn set_sampling_mode<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    global: Var,
    mode: SamplingMode,
) {
    let variables = ctx.part_mut(VariablesP);

    if variables.var_data[global.index()].sampling_mode == mode {
        return;
    }

    variables.var_data[global.index()].sampling_mode = mode;

    if mode == SamplingMode::Hide {
        if let Some(user) = variables.user_from_global_mut().remove(global) {
            variables.user_freelist.push(user);
        }

        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::UserVarName { global, user: None },
        );
    }

    // TODO this also needs to inform Proof when changing between witness and sample
}

/// Initialize a newly allocated solver variable
pub fn initialize_solver_var(
    mut ctx: partial!(
        Context,
        mut AssignmentP,
        mut ImplGraphP,
        mut VsidsP,
        VariablesP
    ),
    solver: Var,
    global: Var,
) {
    let (variables, mut ctx) = ctx.split_part(VariablesP);
    let data = &variables.var_data[global.index()];

    // This recovers the state of a variable that has a known value and was already propagated. This
    // is important so that when new clauses containing this variable are added, load_clause knows
    // to reenqueue the assignment.
    ctx.part_mut(AssignmentP).set_var(solver, data.unit);
    if data.unit.is_some() {
        ctx.part_mut(ImplGraphP).update_removed_unit(solver);
    }
    decision::initialize_var(ctx.borrow(), solver, data.unit.is_none());

    // TODO unhiding beyond unit clauses
}

/// Remove a solver var.
///
/// If the variable is isolated and hidden, the global variable is also removed.
pub fn remove_solver_var<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP, mut VsidsP),
    solver: Var,
) {
    decision::remove_var(ctx.borrow(), solver);

    let variables = ctx.part_mut(VariablesP);

    let global = variables
        .global_from_solver_mut()
        .remove(solver)
        .expect("no existing global var for solver var");

    let data = &mut variables.var_data[global.index()];

    // TODO this check should also be done when a variable is hidden
    if data.sampling_mode == SamplingMode::Hide && data.isolated {
        data.deleted = true;
        // The user isn't interested in the variable and it cannot influence other variables
        debug_assert!(variables.user_from_global().get(global).is_none());

        proof::add_step(ctx.borrow(), false, &ProofStep::DeleteVar { var: global });

        // TODO deletion of unit clauses isn't supported by most DRAT checkers, needs an extra
        // variable mapping instead.

        ctx.part_mut(VariablesP).global_freelist.push(global);
    } else {
        // Remove the mapping, keep the global var
        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::SolverVarName {
                global,
                solver: None,
            },
        );
    }
}
