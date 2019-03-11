//! The reluctant doubling Luby sequence.
//!
//! This sequence is [A182105](https://oeis.org/A182105).

/// Infinite iterator yielding the Luby sequence.
pub struct LubySequence {
    u: u64,
    v: u64,
}

impl Default for LubySequence {
    fn default() -> LubySequence {
        LubySequence { u: 1, v: 1 }
    }
}

impl LubySequence {
    /// Yields the next number of hte Luby sequence.
    pub fn advance(&mut self) -> u64 {
        let result = self.v;

        // Method by Knuth 2012
        if (self.u & self.u.wrapping_neg()) == self.v {
            self.u += 1;
            self.v = 1;
        } else {
            self.v <<= 1;
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence() {
        let mut luby = LubySequence::default();
        let initial_terms: Vec<_> = std::iter::repeat_with(|| luby.advance()).take(64).collect();

        assert_eq!(
            initial_terms,
            vec![
                1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2,
                4, 8, 16, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1,
                2, 1, 1, 2, 4, 8, 16, 32, 1,
            ]
        )
    }
}
