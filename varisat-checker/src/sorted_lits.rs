use varisat_formula::Lit;

/// Sort literals, remove duplicates and check for tautologic clauses.
///
/// Return true if the clause is a tautology
pub fn copy_canonical(target: &mut Vec<Lit>, src: &[Lit]) -> bool {
    target.clear();
    target.extend_from_slice(src);
    target.sort();
    target.dedup();

    let mut last = None;

    target.iter().any(|&lit| {
        let tautology = last == Some(!lit);
        last = Some(lit);
        tautology
    })
}

/// Test whether a set of literals is a (strict) subset of another set of literals
///
/// Requires subset and superset to be sorted.
pub fn is_subset(mut subset: &[Lit], mut superset: &[Lit], strict: bool) -> bool {
    // We set is_strict to true if we don't require a strict subset
    let mut is_strict = !strict;

    while let Some((&sub_min, sub_rest)) = subset.split_first() {
        if let Some((&super_min, super_rest)) = superset.split_first() {
            if sub_min < super_min {
                // sub_min is not in superset
                return false;
            } else if sub_min > super_min {
                // super_min is not in subset, skip it
                superset = super_rest;
                is_strict = true;
            } else {
                // sub_min == super_min, go to next element
                superset = super_rest;
                subset = sub_rest;
            }
        } else {
            // sub_min is not in superset
            return false;
        }
    }
    is_strict |= !superset.is_empty();
    is_strict
}
