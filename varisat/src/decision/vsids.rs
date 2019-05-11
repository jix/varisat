//! The VSIDS branching heuristic.
//!
//! The VSIDS (Variable State Independent Decaying Sum) branching heuristic keeps an activity value
//! for each variable. For each conflict some variables are bumped, which means that their activity
//! is increased by a constant. After bumping some variables, the activity of all variables is
//! decayed by multiplying it with a constant below 1.
//!
//! When a decision is made, it branches on the vairable with the highest activity among the
//! unassigned variables.
//!
//! There are a few variants that differ in which variables are bumped. Varisat follows Minisat (and
//! others) by bumping all variables in the conflict clause and all variables resolved on during
//! conflict analysis.

use ordered_float::OrderedFloat;

use crate::config::SolverConfig;
use crate::lit::Var;

/// The VSIDS branching heuristic.
///
/// As an optimization instead of decaying all activities each conflict, the bump value is divided
/// by the decay factor each conflict. When this would cause a value to overflow all activities and
/// the bump value are scaled down. Apart from a scaling factor that is the same for all involved
/// values, this is equivalent to the naive implementation. As we only care about the order of
/// activities we can ignore the scaling factor.
pub struct Vsids {
    /// The activity of each variable.
    activity: Vec<OrderedFloat<f32>>,
    /// A binary heap of the variables.
    heap: Vec<Var>,
    /// The position in the binary heap for each variable.
    position: Vec<Option<usize>>,
    /// The value to add on bumping.
    bump: f32,
    /// The inverse of the decay factor.
    inv_decay: f32,
}

impl Default for Vsids {
    fn default() -> Vsids {
        Vsids {
            activity: vec![],
            heap: vec![],
            position: vec![],
            bump: 1.0,
            inv_decay: 1.0 / SolverConfig::default().vsids_decay,
        }
    }
}

impl Vsids {
    /// Update structures for a new variable count.
    pub fn set_var_count(&mut self, count: usize) {
        let old_count = self.activity.len();
        debug_assert!(!self.heap.iter().any(|&v| v.index() >= count));
        self.activity.resize(count, OrderedFloat(0.0));
        self.position.resize(count, None);

        for i in old_count..count {
            self.make_available(Var::from_index(i));
        }
    }

    /// Rescale activities if any value exceeds this value.
    fn rescale_limit() -> f32 {
        std::f32::MAX / 16.0
    }

    /// Change the decay factor.
    pub fn set_decay(&mut self, decay: f32) {
        assert!(decay < 1.0);
        assert!(decay > 1.0 / 16.0);
        self.inv_decay = 1.0 / decay;
    }

    /// Bump a variable by increasing its activity.
    pub fn bump(&mut self, var: Var) {
        let rescale = {
            let value = &mut self.activity[var.index()];
            value.0 += self.bump;
            value.0 >= Self::rescale_limit()
        };
        if rescale {
            self.rescale();
        }
        if let Some(pos) = self.position[var.index()] {
            self.sift_up(pos);
        }
    }

    /// Decay all variable activities.
    pub fn decay(&mut self) {
        self.bump *= self.inv_decay;
        if self.bump >= Self::rescale_limit() {
            self.rescale();
        }
    }

    /// Rescale all values to avoid an overflow.
    fn rescale(&mut self) {
        let rescale_factor = 1.0 / Self::rescale_limit();
        for activity in &mut self.activity {
            activity.0 *= rescale_factor;
        }
        self.bump *= rescale_factor;
    }

    /// Insert a variable into the heap if not already present.
    pub fn make_available(&mut self, var: Var) {
        if self.position[var.index()].is_none() {
            let position = self.heap.len();
            self.position[var.index()] = Some(position);
            self.heap.push(var);
            self.sift_up(position);
        }
    }

    /// Move a variable closer to the root until the heap property is satisfied.
    fn sift_up(&mut self, mut pos: usize) {
        let var = self.heap[pos];
        loop {
            if pos == 0 {
                return;
            }
            let parent_pos = (pos - 1) / 2;
            let parent_var = self.heap[parent_pos];
            if self.activity[parent_var.index()] >= self.activity[var.index()] {
                return;
            }
            self.position[var.index()] = Some(parent_pos);
            self.heap[parent_pos] = var;
            self.position[parent_var.index()] = Some(pos);
            self.heap[pos] = parent_var;
            pos = parent_pos;
        }
    }

    /// Move a variable away from the root until the heap property is satisfied.
    fn sift_down(&mut self, mut pos: usize) {
        let var = self.heap[pos];
        loop {
            let mut largest_pos = pos;
            let mut largest_var = var;

            let left_pos = pos * 2 + 1;
            if left_pos < self.heap.len() {
                let left_var = self.heap[left_pos];

                if self.activity[largest_var.index()] < self.activity[left_var.index()] {
                    largest_pos = left_pos;
                    largest_var = left_var;
                }
            }

            let right_pos = pos * 2 + 2;
            if right_pos < self.heap.len() {
                let right_var = self.heap[right_pos];

                if self.activity[largest_var.index()] < self.activity[right_var.index()] {
                    largest_pos = right_pos;
                    largest_var = right_var;
                }
            }

            if largest_pos == pos {
                return;
            }

            self.position[var.index()] = Some(largest_pos);
            self.heap[largest_pos] = var;
            self.position[largest_var.index()] = Some(pos);
            self.heap[pos] = largest_var;
            pos = largest_pos;
        }
    }
}

impl Iterator for Vsids {
    type Item = Var;

    fn next(&mut self) -> Option<Var> {
        if self.heap.is_empty() {
            None
        } else {
            let var = self.heap.swap_remove(0);
            if !self.heap.is_empty() {
                let top_var = self.heap[0];
                self.position[top_var.index()] = Some(0);
                self.sift_down(0);
            }
            self.position[var.index()] = None;
            Some(var)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rescale_bump() {
        let mut vsids = Vsids::default();
        vsids.set_var_count(4);
        vsids.set_decay(1.0 / 8.0);

        for _ in 0..4 {
            vsids.next();
        }

        for i in 0..4 {
            for _ in 0..i {
                vsids.bump(Var::from_index(i));
            }
        }

        for _ in 0..41 {
            vsids.decay();
        }

        for _ in 0..30 {
            vsids.bump(var!(4));
        }

        // Decay is a power of two so these values are exact
        assert_eq!(vsids.activity[0].0, 0.0);
        assert_eq!(vsids.activity[2].0, vsids.activity[1].0 * 2.0);
        assert!(vsids.activity[3] > vsids.activity[2]);
    }

    #[test]
    fn rescale_decay() {
        let mut vsids = Vsids::default();
        vsids.set_var_count(4);
        vsids.set_decay(1.0 / 8.0);

        for _ in 0..4 {
            vsids.next();
        }

        for i in 0..4 {
            for _ in 0..i {
                vsids.bump(Var::from_index(i));
            }
        }

        for _ in 0..60 {
            vsids.decay();
        }

        // Decay is a power of two so these values are exact
        assert_eq!(vsids.activity[0].0, 0.0);
        assert_eq!(vsids.activity[2].0, vsids.activity[1].0 * 2.0);
        assert_eq!(vsids.activity[3].0, vsids.activity[1].0 * 3.0);
    }

    #[test]
    fn heap_sorts() {
        let mut vsids = Vsids::default();
        vsids.set_var_count(8);

        for _ in 0..8 {
            vsids.next();
        }

        for i in 0..8 {
            for _ in 0..i {
                vsids.bump(Var::from_index(i));
            }
        }

        for i in 0..8 {
            vsids.make_available(Var::from_index((i * 5) % 8));
        }

        for i in (0..8).rev() {
            assert_eq!(vsids.next(), Some(Var::from_index(i)));
        }
        assert_eq!(vsids.next(), None);
    }

    #[test]
    fn heap_bump() {
        let mut vsids = Vsids::default();
        vsids.set_var_count(8);
        vsids.set_decay(1.0 / 8.0);

        for _ in 0..8 {
            vsids.next();
        }

        for i in 0..8 {
            for _ in 0..i {
                vsids.bump(Var::from_index(i));
            }
        }

        for i in 0..8 {
            vsids.make_available(Var::from_index((i * 5) % 8));
        }

        for i in (0..4).rev() {
            assert_eq!(vsids.next(), Some(Var::from_index(i + 4)));
        }

        vsids.decay();
        vsids.decay();

        for i in 0..8 {
            for _ in 0..(8 - i) {
                vsids.bump(Var::from_index(i));
            }
        }

        for i in 0..4 {
            assert_eq!(vsids.next(), Some(Var::from_index(i)));
        }

        assert_eq!(vsids.next(), None);
    }
}
