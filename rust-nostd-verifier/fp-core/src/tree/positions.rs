//! `PositionList`, ported from `blocks/tree/positions.h`.
//!
//! A list keeps the sorted set of drawn positions and the draws in order. A non-empty list comes
//! from `from_draws()`. The mark identifies the chain that drew it; a list made by `from_draws()`
//! carries none.

use alloc::vec::Vec;

use crate::chain::public::PublicMark;
use crate::code::short_position::short_position;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PositionList {
    x: Vec<u64>,
    draws: Vec<u64>,
    log_n: u32,
    pub(crate) drawn_by: Option<PublicMark>,
}

impl PositionList {
    /// At least one draw, each below `2^log_n`.
    pub fn from_draws(draws: Vec<u64>, log_n: u32) -> Self {
        assert!(log_n < 64, "positions: the range must be 2^k with k below 64");
        assert!(!draws.is_empty(), "positions: a list needs at least one draw");
        let mut sorted = draws.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert!(sorted[sorted.len() - 1] >> log_n == 0, "positions: a draw outside the range");
        PositionList { x: sorted, draws, log_n, drawn_by: None }
    }

    pub fn log_n(&self) -> u32 {
        self.log_n
    }
    pub fn size(&self) -> usize {
        self.x.len()
    }
    pub fn is_empty(&self) -> bool {
        self.x.is_empty()
    }
    pub fn at(&self, i: usize) -> u64 {
        self.x[i]
    }
    pub fn all(&self) -> &[u64] {
        &self.x
    }
    pub fn draws(&self) -> &[u64] {
        &self.draws
    }

    /// The short positions, sorted and without duplicates.
    pub fn short_positions(&self, log_short: u32) -> Vec<u64> {
        assert!(log_short <= self.log_n, "positions: rows longer than the list's range");
        let mut y: Vec<u64> = self.x.iter().map(|&p| short_position(self.log_n, log_short, p)).collect();
        y.sort_unstable();
        y.dedup();
        y
    }

    /// The same checks: the set is compared, not the draws' order or repeats.
    pub fn same_set(&self, o: &PositionList) -> bool {
        self.log_n == o.log_n && self.x == o.x
    }

    /// `short_list()`: the short positions of the draws, in the same order, with the mark.
    pub fn short_list(&self, log_short: u32) -> PositionList {
        assert!(log_short <= self.log_n, "positions: rows longer than the list's range");
        let y: Vec<u64> = self
            .draws
            .iter()
            .map(|&p| short_position(self.log_n, log_short, p))
            .collect();
        let mut l = PositionList::from_draws(y, log_short);
        l.drawn_by = self.drawn_by.clone();
        l
    }

    /// `part()`: draws `first .. first + count`.
    pub fn part(&self, first: usize, count: usize) -> PositionList {
        assert!(
            count >= 1 && first <= self.draws.len() && count <= self.draws.len() - first,
            "positions: a part beyond the list's draws"
        );
        let mut l = PositionList::from_draws(self.draws[first..first + count].to_vec(), self.log_n);
        l.drawn_by = self.drawn_by.clone();
        l
    }

    /// The index of `x` in `all()`.
    pub fn index_of(&self, x: u64) -> usize {
        Self::index_in(&self.x, x)
    }

    /// The index of `y` in a sorted vector; the order is not checked.
    pub fn index_in(sorted: &[u64], y: u64) -> usize {
        let at = sorted.binary_search(&y).expect("positions: asked for a position that is not in the list");
        at
    }
}
