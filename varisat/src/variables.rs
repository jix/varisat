//! Variable mapping and metadata.

use hashbrown::HashSet;

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
    /// User variables that were explicitly hidden by the user.
    user_freelist: HashSet<Var>,
    /// Global variables that can be recycled without increasing the global_watermark.
    global_freelist: HashSet<Var>,
    /// Solver variables that are unused and can be recycled.
    solver_freelist: HashSet<Var>,

    /// Variable metadata.
    ///
    /// Indexed by global variable indices.
    var_data: Vec<VarData>,
}

impl Default for Variables {
    fn default() -> Variables {
        Variables {
            global_from_user: VarBiMap::default(),
            solver_from_global: VarBiMap::default(),
            user_freelist: Default::default(),
            global_freelist: Default::default(),
            solver_freelist: Default::default(),

            var_data: vec![],
        }
    }
}

impl Variables {
    /// Number of allocated solver variables.
    pub fn solver_watermark(&self) -> usize {
        self.global_from_solver().watermark()
    }

    /// Number of allocated global variables.
    pub fn global_watermark(&self) -> usize {
        self.var_data.len()
    }

    /// Number of allocated global variables.
    pub fn user_watermark(&self) -> usize {
        self.global_from_user().watermark()
    }

    /// Iterator over all user variables that are in use.
    pub fn user_var_iter<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        let global_from_user = self.global_from_user.fwd();
        (0..self.global_from_user().watermark())
            .map(|user_index| Var::from_index(user_index))
            .filter(move |&user_var| global_from_user.get(user_var).is_some())
    }

    /// Iterator over all global variables that are in use.
    pub fn global_var_iter<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        (0..self.global_watermark())
            .map(|global_index| Var::from_index(global_index))
            .filter(move |&global_var| !self.var_data[global_var.index()].deleted)
    }

    /// The user to global mapping.
    pub fn global_from_user(&self) -> &VarMap {
        &self.global_from_user.fwd()
    }

    /// Mutable user to global mapping.
    pub fn global_from_user_mut(&mut self) -> VarBiMapMut {
        self.global_from_user.fwd_mut()
    }

    /// The global to solver mapping.
    pub fn solver_from_global(&self) -> &VarMap {
        &self.solver_from_global.fwd()
    }

    /// Mutable global to solver mapping.
    pub fn solver_from_global_mut(&mut self) -> VarBiMapMut {
        self.solver_from_global.fwd_mut()
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

    /// Mutable  solver to global mapping.
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

    /// Mutable reference to the var data for a global variable.
    pub fn var_data_global_mut(&mut self, global: Var) -> &mut VarData {
        if self.var_data.len() <= global.index() {
            self.var_data.resize(global.index() + 1, VarData::default());
        }
        &mut self.var_data[global.index()]
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

    /// Get an unmapped global variable.
    pub fn next_unmapped_global(&self) -> Var {
        self.global_freelist
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| Var::from_index(self.global_watermark()))
    }

    /// Get an unmapped global variable.
    pub fn next_unmapped_solver(&self) -> Var {
        self.solver_freelist
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| Var::from_index(self.solver_watermark()))
    }

    /// Get an unmapped user variable.
    pub fn next_unmapped_user(&self) -> Var {
        self.user_freelist
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| Var::from_index(self.user_watermark()))
    }
}

/// Maps a user variable into a global variable.
///
/// If no matching global variable exists a new global variable is allocated.
pub fn global_from_user<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    user: Var,
) -> Var {
    let variables = ctx.part_mut(VariablesP);

    if user.index() > variables.user_watermark() {
        // TODO use a batch proof step for this?
        for index in variables.user_watermark()..user.index() {
            global_from_user(ctx.borrow(), Var::from_index(index));
        }
    }

    let variables = ctx.part_mut(VariablesP);

    match variables.global_from_user().get(user) {
        Some(global) => global,
        None => {
            // Can we add an identity mapping?
            let global = if variables.user_from_global().get(user).is_none() {
                user
            } else {
                variables.next_unmapped_user()
            };

            *variables.var_data_global_mut(global) = VarData::user_default();

            variables.global_from_user_mut().insert(global, user);
            variables.global_freelist.remove(&global);
            variables.user_freelist.remove(&user);

            proof::add_step(
                ctx.borrow(),
                false,
                &ProofStep::UserVarName {
                    global,
                    user: Some(user),
                },
            );

            global
        }
    }
}

/// Maps an existing global variable to a solver variable.
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

    debug_assert!(!variables.var_data[global.index()].deleted);

    match variables.solver_from_global().get(global) {
        Some(solver) => solver,
        None => {
            let solver = variables.next_unmapped_solver();

            let old_watermark = variables.global_from_solver().watermark();

            variables.solver_from_global_mut().insert(solver, global);
            variables.solver_freelist.remove(&solver);

            let new_watermark = variables.global_from_solver().watermark();

            if new_watermark > old_watermark {
                set_var_count(ctx.borrow(), new_watermark);
            }

            initialize_solver_var(ctx.borrow(), solver, global);

            proof::add_step(
                ctx.borrow(),
                false,
                &ProofStep::SolverVarName {
                    global,
                    solver: Some(solver),
                },
            );

            solver
        }
    }
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
    let user_var = variables.next_unmapped_user();
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
            variables.user_freelist.insert(user);
        }

        proof::add_step(
            ctx.borrow(),
            false,
            &ProofStep::UserVarName { global, user: None },
        );

        delete_global_if_unused(ctx.borrow(), global);
    }

    // TODO this also needs to inform Proof when changing between witness and sample
    // TODO this needs to allocate a user var when a hidden variable is made user visible
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

    variables.solver_freelist.insert(solver);

    proof::add_step(
        ctx.borrow(),
        false,
        &ProofStep::SolverVarName {
            global,
            solver: None,
        },
    );

    delete_global_if_unused(ctx.borrow(), global);
}

/// Delete a global variable if it is unused
fn delete_global_if_unused<'a>(
    mut ctx: partial!(Context<'a>, mut ProofP<'a>, mut SolverStateP, mut VariablesP),
    global: Var,
) {
    let variables = ctx.part_mut(VariablesP);

    if variables.user_from_global().get(global).is_some() {
        return;
    }

    if variables.solver_from_global().get(global).is_some() {
        return;
    }

    let data = &mut variables.var_data[global.index()];

    assert!(data.sampling_mode == SamplingMode::Hide);

    if !data.isolated {
        return;
    }

    data.deleted = true;

    proof::add_step(ctx.borrow(), false, &ProofStep::DeleteVar { var: global });

    // TODO deletion of unit clauses isn't supported by most DRAT checkers, needs an extra
    // variable mapping instead.

    ctx.part_mut(VariablesP).global_freelist.insert(global);
}
