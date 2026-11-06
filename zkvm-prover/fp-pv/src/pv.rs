//! `FPV1`: the fixed 128-byte public-values block.
//!
//! The guest commits this block first, before the human-readable report and the call's exit
//! status, with `sp1_zkvm::io::commit_slice`: raw bytes and no length prefix, so the block starts
//! at offset 0 of the SP1 public values. `decode` reads those fixed offsets and the contract reads
//! the same ones. Offsets are fixed and reserved bytes must be zero, so there is exactly one
//! encoding of a given verdict.
//!
//! ```text
//! offset size field
//! 0      4    magic "FPV1" (0x46 0x50 0x56 0x31)
//! 4      2    schema_version, big-endian, 1
//! 6      2    reserved, zero
//! 8      1    verdict (1 YES, 2 WITHIN_LIMITS, 3 NO, 4 NOT_A_VERIFICATION, 5 NOT_CHECKED)
//! 9      1    reserved, zero
//! 10     2    call_status, big-endian (the call's exit status)
//! 12     4    result_v1_status, big-endian (the `status=` field of result-v1; 0 if no line)
//! 16     32   commitment_id (the ID the proof was checked against, hex-decoded)
//! 48     32   input_digest (fp_pv::input_digest over the ten inputs)
//! 80     32   result_v1_digest (SHA-256 of the result-v1 line, newline excluded; zero if absent)
//! 112    16   reserved, zero
//! ```

use crate::sha256::sha256;

pub const PV_LEN: usize = 128;
pub const MAGIC: [u8; 4] = *b"FPV1";
pub const SCHEMA_VERSION: u16 = 1;

/// Verdict codes. The contract's accepted-verdict mask has bit `code` set for each accepted code.
pub mod verdict {
    pub const UNSPECIFIED: u8 = 0;
    pub const YES: u8 = 1;
    pub const WITHIN_LIMITS: u8 = 2;
    pub const NO: u8 = 3;
    pub const NOT_A_VERIFICATION: u8 = 4;
    pub const NOT_CHECKED: u8 = 5;

    #[must_use]
    pub fn name(code: u8) -> &'static str {
        match code {
            YES => "YES",
            WITHIN_LIMITS => "WITHIN_LIMITS",
            NO => "NO",
            NOT_A_VERIFICATION => "NOT_A_VERIFICATION",
            NOT_CHECKED => "NOT_CHECKED",
            _ => "UNSPECIFIED",
        }
    }

    /// True for the two verdicts that `cp_verify` treats as an accepted call. The on-chain
    /// deployment decides which of them it accepts; this is only the protocol's own reading.
    #[must_use]
    pub fn is_accepted(code: u8) -> bool {
        code == YES || code == WITHIN_LIMITS
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Values {
    pub verdict: u8,
    pub call_status: u16,
    pub result_v1_status: u32,
    pub commitment_id: [u8; 32],
    pub input_digest: [u8; 32],
    pub result_v1_digest: [u8; 32],
}

impl Values {
    #[must_use]
    pub fn encode(&self) -> [u8; PV_LEN] {
        let mut out = [0u8; PV_LEN];
        out[0..4].copy_from_slice(&MAGIC);
        out[4..6].copy_from_slice(&SCHEMA_VERSION.to_be_bytes());
        out[8] = self.verdict;
        out[10..12].copy_from_slice(&self.call_status.to_be_bytes());
        out[12..16].copy_from_slice(&self.result_v1_status.to_be_bytes());
        out[16..48].copy_from_slice(&self.commitment_id);
        out[48..80].copy_from_slice(&self.input_digest);
        out[80..112].copy_from_slice(&self.result_v1_digest);
        out
    }

    /// Decodes the first 128 bytes. Returns `None` for a wrong length, magic, version, a
    /// non-zero reserved byte, or a verdict code outside 1..=5.
    #[must_use]
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < PV_LEN {
            return None;
        }
        let b = &bytes[..PV_LEN];
        if b[0..4] != MAGIC {
            return None;
        }
        if u16::from_be_bytes([b[4], b[5]]) != SCHEMA_VERSION {
            return None;
        }
        if b[6] != 0 || b[7] != 0 || b[9] != 0 || b[112..128].iter().any(|&x| x != 0) {
            return None;
        }
        let verdict = b[8];
        if !(verdict::YES..=verdict::NOT_CHECKED).contains(&verdict) {
            return None;
        }
        let mut commitment_id = [0u8; 32];
        commitment_id.copy_from_slice(&b[16..48]);
        let mut input_digest = [0u8; 32];
        input_digest.copy_from_slice(&b[48..80]);
        let mut result_v1_digest = [0u8; 32];
        result_v1_digest.copy_from_slice(&b[80..112]);
        Some(Self {
            verdict,
            call_status: u16::from_be_bytes([b[10], b[11]]),
            result_v1_status: u32::from_be_bytes([b[12], b[13], b[14], b[15]]),
            commitment_id,
            input_digest,
            result_v1_digest,
        })
    }
}

/// The `result-v1` line of a report, without its newline.
#[must_use]
pub fn result_v1_line(report: &str) -> Option<&str> {
    report.lines().find(|line| line.starts_with("result-v1 "))
}

/// The verdict line: the last non-empty line.
#[must_use]
pub fn verdict_of(report: &str) -> u8 {
    let Some(line) = report.lines().rev().find(|line| !line.trim().is_empty()) else {
        return verdict::UNSPECIFIED;
    };
    let line = line.trim_end();
    if line == "YES" {
        verdict::YES
    } else if line.starts_with("WITHIN LIMITS:") {
        verdict::WITHIN_LIMITS
    } else if line.starts_with("NO:") {
        verdict::NO
    } else if line == "NOT-A-VERIFICATION" {
        verdict::NOT_A_VERIFICATION
    } else if line.starts_with("NOT CHECKED:") {
        verdict::NOT_CHECKED
    } else {
        verdict::UNSPECIFIED
    }
}

/// A decimal `name=<digits>` field, terminated by a space or the end of the line.
fn number_field(line: &str, name: &str) -> Option<u64> {
    let bytes = line.as_bytes();
    let mut from = 0;
    while let Some(pos) = line[from..].find(name) {
        let at = from + pos;
        let after = at + name.len();
        if at > 0
            && bytes[at - 1] == b' '
            && bytes.get(after) == Some(&b'=')
            && bytes.get(after + 1).is_some_and(u8::is_ascii_digit)
        {
            let mut i = after + 1;
            let mut value = 0u64;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                value = value.wrapping_mul(10).wrapping_add(u64::from(bytes[i] - b'0'));
                i += 1;
            }
            if i == bytes.len() || bytes[i] == b' ' {
                return Some(value);
            }
        }
        from = after;
    }
    None
}

/// A 64-hex-digit `name=<hex>` field.
fn hex_field(line: &str, name: &str) -> Option<[u8; 32]> {
    let bytes = line.as_bytes();
    let mut from = 0;
    while let Some(pos) = line[from..].find(name) {
        let at = from + pos;
        let after = at + name.len();
        if at > 0 && bytes[at - 1] == b' ' && bytes.get(after) == Some(&b'=') {
            let start = after + 1;
            if start + 64 <= bytes.len()
                && bytes[start..start + 64].iter().all(u8::is_ascii_hexdigit)
                && bytes.get(start + 64).is_none_or(|&b| b == b' ')
            {
                let text = core::str::from_utf8(&bytes[start..start + 64]).ok()?;
                return hex_decode_32(text);
            }
        }
        from = after;
    }
    None
}

/// Decodes exactly 64 hex digits (an optional `0x` prefix is accepted).
#[must_use]
pub fn hex_decode_32(text: &str) -> Option<[u8; 32]> {
    let text = text.trim();
    let text = text.strip_prefix("0x").unwrap_or(text);
    if text.len() != 64 || !text.is_ascii() {
        return None;
    }
    let raw = text.as_bytes();
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = (raw[2 * i] as char).to_digit(16)?;
        let lo = (raw[2 * i + 1] as char).to_digit(16)?;
        *byte = ((hi << 4) | lo) as u8;
    }
    Some(out)
}

/// Lowercase hex, no prefix.
#[must_use]
pub fn hex_encode_32(value: &[u8; 32]) -> [u8; 64] {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = [0u8; 64];
    for (i, byte) in value.iter().enumerate() {
        out[2 * i] = DIGITS[usize::from(byte >> 4)];
        out[2 * i + 1] = DIGITS[usize::from(byte & 0x0f)];
    }
    out
}

/// Builds the public values from a report text (the guest's own report, or `fp-host`'s stdout).
///
/// * `id_asked` is the ID passed on the command line. The commitment ID recorded is the one in
///   the `id=` field of the result-v1 line when that line exists — the ID the stages actually
///   checked — and `id_asked` otherwise (a call that printed no result line was rejected before
///   the ID was established).
/// * `call_status` comes from `status=` on the result-v1 line when present; otherwise it is the
///   status that the reference verifier exits with for that verdict (NO: 1, NOT CHECKED: 5).
/// * `result_v1_digest` is zero when no result-v1 line exists.
#[must_use]
pub fn from_report(report: &str, id_asked: &str, input_digest: [u8; 32]) -> [u8; PV_LEN] {
    let line = result_v1_line(report);
    let verdict = verdict_of(report);
    let line_status = line.and_then(|l| number_field(l, "status"));
    let call_status = match line_status {
        Some(v) if v <= u64::from(u16::MAX) => v as u16,
        _ => match verdict {
            verdict::NO => 1,
            verdict::NOT_A_VERIFICATION => 14,
            verdict::NOT_CHECKED => 5,
            _ => 0,
        },
    };
    let result_v1_status = line_status.unwrap_or(0) as u32;
    let commitment_id = line
        .and_then(|l| hex_field(l, "id"))
        .or_else(|| hex_decode_32(id_asked))
        .unwrap_or([0u8; 32]);
    let result_v1_digest = line.map_or([0u8; 32], |l| sha256(l.as_bytes()));
    Values {
        verdict,
        call_status,
        result_v1_status,
        commitment_id,
        input_digest,
        result_v1_digest,
    }
    .encode()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::format;
    use std::string::String;

    const ID: &str = "79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183";

    fn report(verdict_line: &str, result: Option<&str>) -> String {
        let mut text = String::from("calls: 100\n");
        if let Some(line) = result {
            text.push_str(line);
            text.push('\n');
        }
        text.push_str(verdict_line);
        text.push('\n');
        text
    }

    #[test]
    fn roundtrip() {
        let mut value = [0u8; 32];
        value[31] = 0xab;
        let pv = Values {
            verdict: verdict::YES,
            call_status: 0,
            result_v1_status: 0,
            commitment_id: hex_decode_32(ID).unwrap(),
            input_digest: value,
            result_v1_digest: [7u8; 32],
        }
        .encode();
        let back = Values::decode(&pv).unwrap();
        assert_eq!(back.verdict, verdict::YES);
        assert_eq!(back.commitment_id, hex_decode_32(ID).unwrap());
        assert_eq!(back.input_digest, value);
    }

    #[test]
    fn decode_rejects_noncanonical() {
        let base = Values {
            verdict: verdict::YES,
            call_status: 0,
            result_v1_status: 0,
            commitment_id: [1u8; 32],
            input_digest: [2u8; 32],
            result_v1_digest: [3u8; 32],
        }
        .encode();

        let mut short = base;
        assert!(Values::decode(&short[..127]).is_none());
        short[0] = 0;
        assert!(Values::decode(&short).is_none());
        let mut bad_version = base;
        bad_version[5] = 2;
        assert!(Values::decode(&bad_version).is_none());
        let mut reserved = base;
        reserved[112] = 1;
        assert!(Values::decode(&reserved).is_none());
        let mut bad_verdict = base;
        bad_verdict[8] = 0;
        assert!(Values::decode(&bad_verdict).is_none());
        let mut bad_verdict = base;
        bad_verdict[8] = 6;
        assert!(Values::decode(&bad_verdict).is_none());
    }

    #[test]
    fn yes_report() {
        let result = format!(
            "result-v1 status=0 claim=exact-match id={ID} bits=128 work=0 work-rounds=0 least-round=0.00 least-round-without-work=0.00 commitment-assumed-rounds=0 record=1 r=0 e=8 T=8 tokens=1..7 y=yes policy=exact C=0 theta=0 cap=0 s=0 sh=4 sT=0 F=0 above-clip=0 leaf=0 dw=8 build=abc"
        );
        let text = report("YES", Some(&result));
        assert_eq!(verdict_of(&text), verdict::YES);
        let pv = Values::decode(&from_report(&text, ID, [9u8; 32])).unwrap();
        assert_eq!(pv.verdict, verdict::YES);
        assert_eq!(pv.call_status, 0);
        assert_eq!(pv.result_v1_status, 0);
        assert_eq!(pv.commitment_id, hex_decode_32(ID).unwrap());
        assert_eq!(pv.input_digest, [9u8; 32]);
        assert_eq!(pv.result_v1_digest, sha256(result.as_bytes()));
    }

    #[test]
    fn no_report_has_no_result_line() {
        let text = "NO: KL-length\n";
        let pv = Values::decode(&from_report(text, ID, [0u8; 32])).unwrap();
        assert_eq!(pv.verdict, verdict::NO);
        assert_eq!(pv.call_status, 1);
        assert_eq!(pv.result_v1_digest, [0u8; 32]);
        // The ID was still the one the caller asked for; the verdict is what rejects the call.
        assert_eq!(pv.commitment_id, hex_decode_32(ID).unwrap());
    }

    #[test]
    fn within_limits() {
        let result = format!("result-v1 status=0 claim=policy id={ID} r=0 e=8");
        let text = report("WITHIN LIMITS: policy C=1 theta=2 cap=3 s=4 sh=5", Some(&result));
        let pv = Values::decode(&from_report(&text, ID, [0u8; 32])).unwrap();
        assert_eq!(pv.verdict, verdict::WITHIN_LIMITS);
        assert_eq!(pv.call_status, 0);
    }

    #[test]
    fn not_a_verification_uses_the_line_status() {
        let result = format!("result-v1 status=14 claim=next-token id={ID} r=0 e=8");
        let text = report("NOT-A-VERIFICATION", Some(&result));
        let pv = Values::decode(&from_report(&text, ID, [0u8; 32])).unwrap();
        assert_eq!(pv.verdict, verdict::NOT_A_VERIFICATION);
        assert_eq!(pv.call_status, 14);
        assert_eq!(pv.result_v1_status, 14);
    }

    #[test]
    fn commitment_id_comes_from_the_result_line() {
        let other = "aa".repeat(32);
        let result = format!("result-v1 status=0 id={other} r=0 e=8");
        let text = report("YES", Some(&result));
        let pv = Values::decode(&from_report(&text, ID, [0u8; 32])).unwrap();
        assert_eq!(pv.commitment_id, hex_decode_32(&other).unwrap());
    }

    #[test]
    fn hex_roundtrip() {
        let value: [u8; 32] = core::array::from_fn(|i| (i * 3) as u8);
        let text = hex_encode_32(&value);
        let text = core::str::from_utf8(&text).unwrap();
        assert_eq!(hex_decode_32(text).unwrap(), value);
        assert_eq!(hex_decode_32(&format!("0x{text}")).unwrap(), value);
        assert!(hex_decode_32("zz").is_none());
    }

    #[test]
    fn last_line_wins() {
        let text = "YES\nNO: something\n";
        assert_eq!(verdict_of(text), verdict::NO);
    }
}
