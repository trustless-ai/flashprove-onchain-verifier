//! The state that the hash chains of one checked file share, ported from
//! `blocks/chain/session.h`.
//!
//! A session keeps one `TreeValues` record for each Merkle root (selected by the root's 32 bytes)
//! and one entry for each chain. The port's channels borrow the session mutably, so `accepted()`
//! runs after every channel of the session has been dropped; a channel's `Drop` records a
//! rejection. C++ can ask a live channel's `ok()` through a closure; the borrow makes that
//! question unrepresentable here, and the same verdict is reached at the drop.

use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::vec::Vec;

use super::public::SharedFate;
use crate::hash::modes::Digest;
use crate::tree::tree::TreeValues;

/// One chain's outcome (`Entry`).
struct Entry {
    fate: SharedFate,
}

/// The chains and tree records of one file's check (`VerifierSession`).
#[derive(Default)]
pub struct VerifierSession {
    records: BTreeMap<[u32; 8], TreeValues>,
    chains: Vec<Entry>,
}

impl VerifierSession {
    pub fn new() -> Self {
        Self::default()
    }

    /// The record of the vertices below `root` (`record`).
    pub fn record(&mut self, root: &Digest) -> &mut TreeValues {
        self.records.entry(root.w).or_default()
    }

    pub fn roots(&self) -> usize {
        self.records.len()
    }
    pub fn chains(&self) -> usize {
        self.chains.len()
    }

    /// The verdict (`accepted`).
    pub fn accepted(&self) -> bool {
        assert!(!self.chains.is_empty(), "session: a verdict on no chain");
        for c in &self.chains {
            if c.fate.get().refused {
                return false;
            }
        }
        for c in &self.chains {
            assert!(c.fate.get().ended, "session: a chain that was started has not been brought to its end");
        }
        true
    }

    pub(crate) fn enter(&mut self, fate: SharedFate) {
        self.chains.push(Entry { fate });
    }

    /// The live-channel closure of the C++ entry is gone; the entry stays for the verdict.
    pub(crate) fn leave(&mut self, _fate: &SharedFate) {}

    pub(crate) fn holds(&self, fate: &SharedFate) -> bool {
        self.chains.iter().any(|c| Rc::ptr_eq(&c.fate, fate))
    }
}
