//! Header checks and the parameter file's version line.
//!
//! Ported from `verifier/src/vf_input_files.h:19-53` and `verifier/src/cp_verify.cpp:3222-3227`.
//! `cpConfRead()` (the configuration folder's `lstat` and file reads) is host I/O and stays in
//! `fp-host`; everything in this module is a pure function of bytes.

use crate::consts::{PROGRAM_VERSION_WORD, TAG_KEY, TAG_PROOF};
use crate::refusal::{Refusal, Result};

/// Header lengths in 32-bit words (`vf_input_files.h:17`).
pub const CP_KEY_HEADW: usize = 2;
pub const CP_PROOF_HEADW: usize = 3;

/// Little-endian 32-bit word `i` of a file's bytes (`vf_input_files.h:20-23`).
///
/// Precondition, as in C++: `4 * i + 4 <= b.len()`. Callers check the length first.
pub fn cp_word(b: &[u8], i: usize) -> u32 {
    let at = 4 * i;
    let p = &b[at..at + 4];
    u32::from_le_bytes([p[0], p[1], p[2], p[3]])
}

/// Checks `key.bin`'s header (`vf_input_files.h:26-29`).
///
/// `ver` is the version word of the caller's `policy.txt` (`cp_policy_word`).
pub fn cp_key_head(b: &[u8], ver: u32) -> Result<()> {
    if b.len() < 4 * CP_KEY_HEADW {
        return Err(Refusal::named("cp-key-length"));
    }
    if cp_word(b, 0) != TAG_KEY || cp_word(b, 1) != ver {
        return Err(Refusal::named("cp-key-head"));
    }
    Ok(())
}

/// Checks a proof file's header and returns the leaf number `k`, unchecked
/// (`vf_input_files.h:48-53`). A `k` without a leaf file is `cp-entry-missing`.
pub fn cp_proof_head(b: &[u8], ver: u32) -> Result<u32> {
    if b.len() < 4 * CP_PROOF_HEADW {
        return Err(Refusal::named("cp-proof-length"));
    }
    if cp_word(b, 0) != TAG_PROOF || cp_word(b, 1) != ver {
        return Err(Refusal::named("cp-proof-head"));
    }
    Ok(cp_word(b, 2))
}

/// `version_from_text()` (`blocks/frame/version.h:37-41`): four bytes, first in the low byte.
/// Returns 0 for a text of another length, as C++ does.
pub fn version_from_text(s: &[u8]) -> u32 {
    if s.len() != 4 {
        return 0;
    }
    (s[0] as u32) | ((s[1] as u32) << 8) | ((s[2] as u32) << 16) | ((s[3] as u32) << 24)
}

/// `cpPolicyWord()` (`cp_verify.cpp:3222-3227`): the version word on the parameter file's first
/// line, or `NO: version-unknown (policy)`.
///
/// The C++ check is `!pol.compare(0, 8, "version ") && pol.size() > 12 && pol[12] == '\n'`.
pub fn cp_policy_word(pol: &[u8]) -> Result<u32> {
    let has = pol.len() > 12 && pol.starts_with(b"version ") && pol[12] == b'\n';
    let v = if has { version_from_text(&pol[8..12]) } else { 0 };
    if has && v == PROGRAM_VERSION_WORD {
        Ok(v)
    } else {
        Err(Refusal::named("version-unknown (policy)"))
    }
}
