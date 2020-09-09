//! Variable metadata.
use partial_ref::{partial, PartialRef};
use rustc_hash::FxHashSet as HashSet;

use varisat_formula::Var;

use crate::{
    context::{parts::*, Context},
    processing::{process_step, CheckedProofStep, CheckedSamplingMode, CheckedUserVar},
    CheckerError,
};

/// Data for each literal.
#[derive(Clone, Default)]
pub struct LitData {
    pub clause_count: usize,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum SamplingMode {
    Sample,
    Witness,
    Hide,
}

/// Data for each variable.
#[derive(Clone)]
pub struct VarData {
    pub user_var: Option<Var>,
    pub sampling_mode: SamplingMode,
}

impl Default for VarData {
    fn default() -> VarData {
        VarData {
            user_var: None,
            sampling_mode: SamplingMode::Sample,
        }
    }
}

#[derive(Default)]
pub struct Variables {
    /// Information about literals in the current formula.
    pub lit_data: Vec<LitData>,
    /// Information about variables in the current formula.
    pub var_data: Vec<VarData>,
    /// User var names in use.
    ///
    /// This is used to check for colliding mappings which are not allowed.
    used_user_vars: HashSet<Var>,
}

/// Check that var is a sampling user var and create new variables as necessary.
pub fn ensure_sampling_var(
    mut ctx: partial!(Context, mut ClausesP, mut VariablesP, CheckerStateP),
    var: Var,
) -> Result<(), CheckerError> {
    ensure_var(ctx.borrow(), var);

    let variables = ctx.part_mut(VariablesP);

    if variables.var_data[var.index()].sampling_mode != SamplingMode::Sample {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("variable {:?} is not a sampling variable", var),
        ));
    }
    Ok(())
}

/// Ensure that a variable is present.
pub fn ensure_var(mut ctx: partial!(Context, mut ClausesP, mut VariablesP), var: Var) {
    let (variables, mut ctx) = ctx.split_part_mut(VariablesP);

    if variables.var_data.len() <= var.index() {
        variables
            .var_data
            .resize(var.index() + 1, VarData::default());
        variables
            .lit_data
            .resize((var.index() + 1) * 2, LitData::default());
        ctx.part_mut(ClausesP)
            .unit_clauses
            .resize(var.index() + 1, None);
    }
}

/// Add a user/global var mapping.
pub fn add_user_mapping<'a>(
    mut ctx: partial!(Context<'a>, mut ClausesP, mut ProcessingP<'a>, mut VariablesP, CheckerStateP),
    global_var: Var,
    user_var: Var,
) -> Result<(), CheckerError> {
    ensure_var(ctx.borrow(), global_var);

    let mut ctx_in = ctx;
    let (variables, ctx) = ctx_in.split_part_mut(VariablesP);

    // TODO will the first check cause problems when observing solver added variables?
    // That check is required for the workaround in CheckerData's user from proof method
    if user_var.index() >= variables.var_data.len() || variables.used_user_vars.contains(&user_var)
    {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("user name {:?} used for two different variables", user_var),
        ));
    }

    let var_data = &mut variables.var_data[global_var.index()];

    // sampling_mode will be Witness for a newly observed internal variable and Sample for a a
    // fresh variable
    if var_data.sampling_mode == SamplingMode::Hide {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!(
                "user name added to variable {:?} which is still hidden",
                global_var
            ),
        ));
    }

    if var_data.user_var.is_some() {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("change of user name for in use varible {:?}", global_var),
        ));
    }

    var_data.user_var = Some(user_var);

    variables.used_user_vars.insert(user_var);

    let sampling_mode = if var_data.sampling_mode == SamplingMode::Witness {
        CheckedSamplingMode::Witness
    } else {
        CheckedSamplingMode::Sample
    };

    process_step(
        ctx_in.borrow(),
        &CheckedProofStep::UserVar {
            var: global_var,
            user_var: Some(CheckedUserVar {
                user_var,
                sampling_mode,
                new_var: true,
            }),
        },
    )?;

    Ok(())
}

/// Remove a user/global var mapping.
pub fn remove_user_mapping<'a>(
    mut ctx: partial!(Context<'a>, mut ClausesP, mut ProcessingP<'a>, mut VariablesP, CheckerStateP),
    global_var: Var,
) -> Result<(), CheckerError> {
    ensure_var(ctx.borrow(), global_var);

    let variables = ctx.part_mut(VariablesP);

    let var_data = &variables.var_data[global_var.index()];

    // We process this step before removing the mapping, so the processor can still look up the
    // mapping.

    if var_data.user_var.is_some() {
        process_step(
            ctx.borrow(),
            &CheckedProofStep::UserVar {
                var: global_var,
                user_var: None,
            },
        )?;
    } else {
        return Err(CheckerError::check_failed(
            ctx.part(CheckerStateP).step,
            format!("no user name to remove for variable {:?}", global_var),
        ));
    }

    let variables = ctx.part_mut(VariablesP);

    let var_data = &mut variables.var_data[global_var.index()];
    if let Some(user_var) = var_data.user_var {
        variables.used_user_vars.remove(&user_var);
        var_data.user_var = None;
        var_data.sampling_mode = SamplingMode::Hide;
    }

    Ok(())
}
