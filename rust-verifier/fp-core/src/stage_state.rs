//! Everything that C++ keeps in file-scope mutable variables across one `runStage()`.
//!
//! C++ can rely on a fresh process per stage (`cpStagesRun()`, `verifier/src/cp_verify.cpp:2670`).
//! The port runs the three stages in one process, so every stage must start from these values.
//! The initial types are minimal placeholders: a later step replaces the accounting and shape members with the
//! real ones, keeping the field names and defaults.
//!
//! The initial list names 16 fields. `run_version_word_fixed` is the required partner of
//! `run_version_word` (`vf_common.h:446-447`): dropping it would make the reset incomplete, so it
//! is the 17th field here.

use alloc::string::String;

use crate::hash::calls::HashCalls;
use crate::consts::{
    GATE_TABLE_INPUT_FRACTION_BITS_DEFAULT, GCL_DEFAULT, INNER_THREADS_DEFAULT, LIDB_SEALED,
    RESIDUAL_STREAM_LIMBS_DEFAULT, RCL_DEFAULT, SMAXTOP, TAU_DEFAULT,
};

/// `WorkNote` (`vf_common.h:741-745`).
#[derive(Clone, Debug, PartialEq)]
pub struct WorkNote {
    pub needed: bool,
    pub bits: f64,
    pub work: u32,
    /// C++ field `where`.
    pub where_: String,
}

impl Default for WorkNote {
    fn default() -> Self {
        Self { needed: false, bits: 0.0, work: 0, where_: String::new() }
    }
}

/// Placeholder for `blk::Accounting` (`blocks/numbers/accounting.h:56-70`).
///
/// The first step only needs a value that can be reset and stored. Later steps fill in groups, lists, closeness
/// terms and the rest.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct AccountingStub {
    pub formed: bool,
    pub holds: bool,
    pub needs_work: bool,
    pub target: u32,
    pub calls: u64,
    pub by_work: u64,
}

/// `TargetBitsWord` (`vf_lookup_helpers.h:109-111`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TargetBitsWord {
    pub at: usize,
    pub hb: u32,
}

/// Placeholder for the `LinkCtx*` kept in `currentSegment` (`vf_subproof_segment.h:151`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinkCtxId(pub u32);

/// Placeholder for the `blk::Shapes*` kept in `stageShapesMade` (`cp_verify.cpp:1213`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapesId(pub u32);

/// The per-stage mutable state.
///
/// Each field carries the C++ source and its initial value. `Default::default()` is the state at
/// the start of a stage; construct a fresh value for each stage.
#[derive(Clone, Debug, PartialEq)]
pub struct StageState {
    /// `TAU`, the smallness test's number of combinations (`vf_common.h:468`).
    pub tau: i32,
    /// `LIDB` (`vf_common.h:529`), initial `LIDB_SEALED`.
    pub lidb: i32,
    /// `NMINH` (`vf_common.h:535`).
    pub nminh: i32,
    /// `POW`, `POWS`, `POWC` (`vf_common.h:537`): bits of work of a request's own rounds, of a
    /// batch's shared, and of the committer's; from the frame line `work` (`cp_verify.cpp:981`).
    pub pow: i32,
    pub pows: i32,
    pub powc: i32,
    /// `stageWorkNote` (`vf_common.h:747`).
    pub stage_work_note: WorkNote,
    /// `acctNote` (`vf_common.h:759`).
    pub acct_note: AccountingStub,
    /// `residualStreamLimbs` (`vf_norm_digit_rows.h:24`).
    pub residual_stream_limbs: i32,
    /// `gateTableInputFractionBits` (`cp_verify.cpp:186`).
    pub gate_table_input_fraction_bits: i32,
    /// `SMAX` (`cp_verify.cpp:186`), initial `SMAXTOP`.
    pub smax: i32,
    /// `RCL` (`cp_verify.cpp:189`).
    pub rcl: i32,
    /// `GCL` (`cp_verify.cpp:193`).
    pub gcl: i32,
    /// `statedTarget` (`vf_lookup_helpers.h:113`).
    pub stated_target: TargetBitsWord,
    /// `currentSegment` (`vf_subproof_segment.h:151`), a thread-local pointer in C++.
    pub current_segment: Option<LinkCtxId>,
    /// `refuseThrows` (`vf_common.h:52`), a thread-local flag in C++.
    pub refuse_throws: bool,
    /// `innerThreads` (`vf_common.h:61`), set from `-j`.
    pub inner_threads: i32,
    /// `runVersionWord` (`vf_common.h:446`).
    pub run_version_word: u32,
    /// `runVersionWordFixed` (`vf_common.h:447`); see the module comment.
    pub run_version_word_fixed: bool,
    /// `stageShapesMade` (`cp_verify.cpp:1213`).
    pub stage_shapes_made: Option<ShapesId>,
    /// The two hash-call counters (`vf_earlier_hash_f.h:57-75`, `blocks/hash/tweak.h:64-70`).
    /// A stage starts them at zero (`cp_verify.cpp:2698-2700`).
    pub hash_calls: HashCalls,
}

impl Default for StageState {
    fn default() -> Self {
        Self {
            tau: TAU_DEFAULT,
            lidb: LIDB_SEALED,
            nminh: 0,
            pow: 0,
            pows: 0,
            powc: 0,
            stage_work_note: WorkNote::default(),
            acct_note: AccountingStub::default(),
            residual_stream_limbs: RESIDUAL_STREAM_LIMBS_DEFAULT,
            gate_table_input_fraction_bits: GATE_TABLE_INPUT_FRACTION_BITS_DEFAULT,
            smax: SMAXTOP,
            rcl: RCL_DEFAULT,
            gcl: GCL_DEFAULT,
            stated_target: TargetBitsWord::default(),
            current_segment: None,
            refuse_throws: false,
            inner_threads: INNER_THREADS_DEFAULT,
            run_version_word: 0,
            run_version_word_fixed: false,
            stage_shapes_made: None,
            hash_calls: HashCalls::new(),
        }
    }
}
