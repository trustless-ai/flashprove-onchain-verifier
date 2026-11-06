//! Constants shared by the verifier core.
//!
//! Every item names its C++ source. The crate must stay `no_std` and must not contain
//! file-scope mutable statics; this module holds `const` values only.

/// 32-bit words in a digest (`verifier/src/vf_digest_words.h:10`).
pub const DW: u32 = 8;
/// The same constant under its build-time name (`verifier/build.sh: -DDIGEST_WORDS=8`).
pub const DIGEST_WORDS: u32 = 8;
/// Hex digits of a printed digest: `HEXW = 8 * DW` (`vf_widths_and_bounds.h:815`).
pub const HEXW: usize = 64;
/// Half a digest's bits, the largest `-bits` accepted (`vf_common.h:333`).
pub const DIGEST_HALF_BITS: f64 = 16.0 * DW as f64;
/// `BAR`, the fewest requested bits with which a call can pass (`vf_common.h:478`).
pub const BAR: f64 = if DW == 8 { 128.0 } else { 136.0 };
/// `THRESHOLD_BITS_TEXT` (`vf_common.h:326`).
pub const THRESHOLD_BITS_TEXT: &str = "128";

/// Four characters packed little-endian, first in the low byte
/// (`blocks/frame/version.h:25`).
pub const fn tag_of(a: u8, b: u8, c: u8, d: u8) -> u32 {
    (a as u32) | ((b as u32) << 8) | ((c as u32) << 16) | ((d as u32) << 24)
}

/// `CPIK` (`blocks/frame/heads.h:31`).
pub const TAG_KEY: u32 = tag_of(b'C', b'P', b'I', b'K');
/// `CPEN` (`blocks/frame/heads.h:31`).
pub const TAG_ENTRY: u32 = tag_of(b'C', b'P', b'E', b'N');
/// `CPPF` (`blocks/frame/heads.h:31`).
pub const TAG_PROOF: u32 = tag_of(b'C', b'P', b'P', b'F');

/// `"H821"`: format 8, Goldilocks (BLK_FIELD=2), BLAKE2b (BLK_HASH=1)
/// (`blocks/frame/version.h:28`, `blocks/base.h:29-37`).
pub const fn version_word(field: u8, hash: u8) -> u32 {
    tag_of(b'H', b'8', b'0' + field, b'0' + hash)
}

/// `BLK_FIELD`, the build's field (`blocks/base.h:29-37`).
pub const BLK_FIELD: u64 = 2;
/// `BLK_HASH`, the build's hash (`blocks/base.h:29-37`).
pub const BLK_HASH: u64 = 1;
/// The only version word this build accepts (`blocks/frame/version.h:28`).
pub const PROGRAM_VERSION_WORD: u32 = version_word(2, 1);
/// The same word as text, for diagnostics.
pub const VERSION_TEXT: &str = "H821";

/// `VF_SOURCE_DIGEST` for this checkout, computed by `verifier/build.sh:311` and verified
/// with that script's exact pipeline in S0.
pub const BUILD_SOURCE_DIGEST: &str =
    "93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595";

// Exit statuses (`verifier/docs/output.md`, "Exit codes"; `verifier/src/cp_verify.cpp:33-42`).
pub const STATUS_YES: i32 = 0;
pub const STATUS_NO: i32 = 1;
pub const STATUS_USAGE_OR_UNREADABLE: i32 = 2;
pub const STATUS_PART_PASSED: i32 = 3;
pub const STATUS_PLAN_ONLY: i32 = 4;
pub const STATUS_NOT_CHECKED: i32 = 5;
pub const STATUS_NOT_A_VERIFICATION: i32 = 14;
pub const STATUS_NOT_WRITTEN: i32 = 15;

// Initial values of the per-stage mutable state (`verifier/src`), repeated here so that
// `StageState::default()` and the C++ globals cannot drift apart unnoticed.
pub const TAU_DEFAULT: i32 = 160; // vf_common.h:468
pub const LIDB_SEALED: i32 = 22; // vf_common.h:526
pub const LIDB_MAX: i32 = 30; // vf_common.h:526
pub const NMINH_MAX: i32 = 28; // vf_common.h:534
pub const RESIDUAL_STREAM_LIMBS_DEFAULT: i32 = 4; // vf_norm_digit_rows.h:24
pub const GATE_TABLE_INPUT_FRACTION_BITS_DEFAULT: i32 = 8; // cp_verify.cpp:186
pub const SMAXTOP: i32 = 4095; // vf_widths_and_bounds.h:40
pub const RCL_DEFAULT: i32 = 0; // cp_verify.cpp:189
pub const GCL_DEFAULT: i32 = 0; // cp_verify.cpp:193
pub const INNER_THREADS_DEFAULT: i32 = 1; // vf_common.h:61
