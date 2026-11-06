//! The matrices of one sub-proof's approximate range check, ported from
//! `verifier/src/vf_smallness_matrices.h`.

use alloc::string::String;
use alloc::vec::Vec;

/// A matrix: `m` cell rows, `k` columns (`struct TMat`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TMat {
    pub name: String,
    pub m: u64,
    pub k: u64,
    /// 0: this sub-proof commits to it; 1: an earlier one. `shapeF` rejects others (2: weight
    /// matrix).
    pub kind: i32,
    /// For `kind` 1 only: the index in `HTailF2::ft` of the earlier sub-proof's symbol tree.
    pub foreign: i32,
    /// The matrix's first column in that tree; `shapeF` rejects a nonzero one.
    pub tt_off: u64,
    /// `256 * gid + mu`: `gid` the owning sub-proof's number, `mu` its index there.
    pub a_id: u64,
    /// The symbol tree's `w`; no parameter-file line sets it.
    pub wp: u32,
}

impl Default for TMat {
    /// The C++ member defaults: `kind` 0, `foreign` -1 (no foreign matrix), no offset.
    fn default() -> Self {
        Self {
            name: String::new(),
            m: 0,
            k: 0,
            kind: 0,
            foreign: -1,
            tt_off: 0,
            a_id: 0,
            wp: 0,
        }
    }
}

/// The fold list of one sub-proof's range check (`struct Tail`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tail {
    pub mats: Vec<TMat>,
}

impl Tail {
    /// `Tail::foldColumns()`.
    pub fn fold_columns(&self) -> u64 {
        self.mats.iter().map(|m| m.k).sum()
    }
}
