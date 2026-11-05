//! Hash-call counters.
//!
//! C++ has two counters: `f2b::calls_total()` (`verifier/src/vf_earlier_hash_f.h:57-75`) and
//! `blk::hash_calls_made` under `BLK_COUNT_HASH_CALLS` (`blocks/hash/tweak.h:64-70`). `cp_verify`
//! adds them for `q_V`. Each stage resets both (`cp_verify.cpp:2698-2700`). The port is
//! single-threaded: the counters are plain `u64`s passed explicitly, not atomics.

/// The two counts of one scope. `f2b` counts the verifier's own BLAKE2b compression; `blk` counts
/// `Blake2bF::compress64()`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HashCalls {
    pub f2b: u64,
    pub blk: u64,
}

impl HashCalls {
    pub const fn new() -> Self {
        Self { f2b: 0, blk: 0 }
    }

    /// `f2b::calls_begin()` plus the reset of `blk::hash_calls_made`: a stage starts at zero.
    pub fn begin(&mut self) {
        self.f2b = 0;
        self.blk = 0;
    }

    /// What `cp_verify` adds: both counters.
    pub fn total(&self) -> u64 {
        self.f2b + self.blk
    }
}
