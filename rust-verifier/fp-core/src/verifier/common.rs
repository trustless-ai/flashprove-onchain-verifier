//! The verifier-reachable core of `verifier/src/vf_common.h`.
//!
//! The C++ header mixes four kinds of code: the verifier's constants and helpers, the standard
//! parameter form and the acceptance policies, the field arithmetic's fast paths, and the host's
//! file, thread and output plumbing. Only the first two and the arithmetic belong in `no_std`
//! `fp-core`; `refuse()` becomes a `Refusal` value, and every function that printed now returns a
//! `String` or the caller's text. File readers, `parFor()`, `now()` and `printf` stay in `fp-host`.
//!
//! The equality tables here keep the C++ `vf_common.h` convention, which is **not** the
//! `blocks/field/mle.h` convention: `z[0]` belongs to the top bit of the index (`eqTab`/`eqOne`),
//! while `mle::eq_table`/`mle::eq_index` put `z[t]` on bit `t`. Do not pass a `vf_common` point to
//! `mle::eq_*`; use `eq_tab`/`eq_one` below.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::consts::PROGRAM_VERSION_WORD;
use crate::field::ext::E;
use crate::field::gl64;
use crate::refusal::{Refusal, Result};
use crate::stage_state::StageState;

// ---------------------------------------------------------------------------------------------
// Constants (`vf_common.h:325-350, 460-537, 769`)
// ---------------------------------------------------------------------------------------------

/// `CE`: components of an element of the challenge field E = F_p[x] / (x^3 - 2)
/// (`vf_common.h:460`).
pub const CE: usize = 3;
/// `WPE`: 32-bit words of one element of E (`vf_common.h:462`).
pub const WPE: usize = 2 * CE;
/// `LE`: `lg |E|`, rounded up (`vf_common.h:463`).
pub const LE: i32 = gl64::BITS as i32 * CE as i32;

/// `IDLINE` (`vf_common.h:499`).
pub const IDLINE: &str = "commitment ID: ";
/// `STAGEIDLINE`, `"computed " IDLINE` (`vf_common.h:500`).
pub const STAGEIDLINE: &str = "computed commitment ID: ";
/// `WORKLINE` (`vf_common.h:502`).
pub const WORKLINE: &str = "proof of work: ";
/// `RESULTWORD` (`vf_common.h:504`).
pub const RESULTWORD: &str = "result-v1";
/// `COMMITMENTLINE` (`vf_common.h:508`).
pub const COMMITMENTLINE: &str = "commitment: ";
/// `ONE_TIME_LINE_START` (`vf_common.h:509`).
pub const ONE_TIME_LINE_START: &str = "accounting: one-time files: ";
/// `RECORDCLAUSE`, the end of a `COMMITMENTLINE` (`vf_common.h:510`).
pub const RECORDCLAUSE: &str = "; the table has a record: the binding of the weights rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given";
/// `IDHIDDEN` (`vf_common.h:513`).
pub const IDHIDDEN: &str = "not-shown-without-id";
/// `WITHINSTATUS` (`vf_common.h:518`).
pub const WITHINSTATUS: i32 = 0;
/// `WITHIN` (`vf_common.h:519`).
pub const WITHIN: &str = "WITHIN LIMITS: ";
/// `NOT_A_VERIFICATION_TEXT` (`vf_common.h:491`).
pub const NOT_A_VERIFICATION_TEXT: &str = "NOT-A-VERIFICATION";
/// `STAGE_PASSED_WITH_WORK_STATUS` (`vf_common.h:769`).
pub const STATUS_STAGE_PASSED_WITH_WORK: i32 = 12;

/// `LBZ` (`vf_common.h:523`): a request's range checks bound Z by beta_z = 2^LBZ.
pub const LBZ: i32 = 17;
/// `LBZW` (`vf_common.h:523-524`).
pub const LBZW: i32 = 20;
/// `WORK_BITS_MOST` (`vf_common.h:605`).
pub const WORK_BITS_MOST: u32 = 32;

/// `TEST_BUILD` (`vf_common.h:541-545`). This build is a serving build, so no test switch is set.
pub const TEST_BUILD: bool = false;

/// `FIELD_P` (`vf_common.h:381`); the same word as `gl64::P`.
pub const FIELD_P: u64 = gl64::P;
/// `FIELD_W` (`vf_common.h:383`); the same constant as `gl64::NR`.
pub const FIELD_W: u64 = gl64::NR;

/// `SERVED_LAYOUT` (`vf_common.h:573`).
pub const SERVED_LAYOUT: &str = "placement-table";
/// `SERVED_TWO_CODES` (`vf_common.h:602-604`).
pub const SERVED_TWO_CODES: &str =
    "two-codes (group folded and group omega or group once-folded and group once-omega have the same code length and message length. The test on the committed table then runs without its split step and the bounds argued on paper for this protocol do not cover that form. See verifier/docs/parameter-file.md)";
/// `SERVED_EXACT` (`vf_common.h:607-609`).
pub const SERVED_EXACT: &str =
    "exact-match (the request covers tokens of its own under another policy than C = theta = 2^sh with cap = 0 and sT = sh - 4 and a pass could say little. See -policy)";
/// `SERVED_NAMED` (`vf_common.h:610-612`).
pub const SERVED_NAMED: &str =
    "policy-named (the option -policy names another kind of policy or another C or theta or cap or s or sh than the parameter file sets. The line covered shows what the file sets)";

// ---------------------------------------------------------------------------------------------
// Small helpers (`vf_common.h:293-378, 480-484`)
// ---------------------------------------------------------------------------------------------

/// Rejects a text file of 2^32 bytes or more (`rejectLongTextFile`, `vf_common.h:322-324`).
pub fn reject_long_text_file(bytes: u64) -> Result<()> {
    if bytes >> 32 != 0 {
        Err(Refusal::named("close-list-long"))
    } else {
        Ok(())
    }
}

/// `textNumber` (`vf_common.h:480-484`): the leading decimal digits of `s`, or 0 if there are none.
pub const fn text_number(s: &str) -> u32 {
    let b = s.as_bytes();
    let mut i = 0usize;
    let mut v = 0u32;
    while i < b.len() && b[i] >= b'0' && b[i] <= b'9' {
        v = v.wrapping_mul(10).wrapping_add((b[i] - b'0') as u32);
        i += 1;
    }
    v
}

/// The SplitMix64 mixer; not cryptographic (`mix64`, `vf_common.h:373-378`).
pub const fn mix64(z: u64) -> u64 {
    let mut z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// `hex64` (`vf_common.h:334-338`): the words as lowercase hex, eight digits each.
pub fn hex64(w: &[u32]) -> String {
    let mut s = String::with_capacity(8 * w.len());
    for x in w {
        s.push_str(&format!("{:08x}", x));
    }
    s
}

/// True if `name` is meant for a program or machine fault: `"internal-"` first, or after a
/// sub-proof's prefix (`"G0:"`) (`internalName`, `vf_common.h:342-346`).
pub fn internal_name(name: &str) -> bool {
    let b = name.as_bytes();
    let mut i = 0usize;
    while i < b.len() && b[i].is_ascii_alphanumeric() {
        i += 1;
    }
    let start = if i != 0 && i < b.len() && b[i] == b':' { i + 1 } else { 0 };
    b[start..].starts_with(b"internal-")
}

/// `decimal()` (`vf_common.h:353-364`): 1 to 7 decimal digits, no leading zero except in `"0"`, at
/// most `max`. `None` is C++'s `false`.
pub fn decimal(arg: &str, max: u32) -> Option<u32> {
    let b = arg.as_bytes();
    if b.is_empty() || b.len() > 7 || (b.len() > 1 && b[0] == b'0') {
        return None;
    }
    let mut v = 0u32;
    for &c in b {
        if !c.is_ascii_digit() {
            return None;
        }
        v = 10 * v + (c - b'0') as u32;
    }
    if v > max {
        None
    } else {
        Some(v)
    }
}

/// `parseRequestedBits()` (`vf_common.h:365-370`).
pub fn parse_requested_bits(arg: &str) -> Option<f64> {
    decimal(arg, 1_000_000).map(|v| v as f64)
}

// ---------------------------------------------------------------------------------------------
// Field fast paths (`vf_common.h:388-427`)
// ---------------------------------------------------------------------------------------------

/// The canonical value mod p of any `v < 2^128` (`fred`/`fredW`, `vf_common.h:388-393`).
#[inline]
pub const fn fred(v: u128) -> u64 {
    gl64::reduce128((v >> 64) as u64, v as u64)
}

/// `fred(p) - fred(n)` for non-negative accumulators, with one reduction instead of two.
/// `(P << 32)` is a multiple of the modulus and exceeds any accumulator below `2^32 * 2^64`
/// (the signed sums built by `fold_sums` are below `tau * 2^64`), and `p + (P << 32) - n` stays
/// inside `u128`, so the result is the same canonical value as the two-reduction difference.
#[inline]
pub const fn fred_diff(p: u128, n: u128) -> u64 {
    fred(p + ((gl64::P as u128) << 32) - n)
}

/// `a + x1 y1`, canonical (`fmad1`, `vf_common.h:405-407`).
#[inline]
pub const fn fmad1(a: u64, x1: u64, y1: u64) -> u64 {
    fred((x1 as u128) * (y1 as u128) + (a as u128))
}

/// `a + x1 y1 + x2 y2`, canonical (`fmad2`, `vf_common.h:408-410`).
#[inline]
pub const fn fmad2(a: u64, x1: u64, y1: u64, x2: u64, y2: u64) -> u64 {
    gl64::add(fmad1(a, x1, y1), gl64::mul(x2, y2))
}

/// `a + x1 y1 + x2 y2 + x3 y3`, canonical (`fmad3`, `vf_common.h:411-413`).
#[inline]
pub const fn fmad3(a: u64, x1: u64, y1: u64, x2: u64, y2: u64, x3: u64, y3: u64) -> u64 {
    gl64::add(fmad2(a, x1, y1, x2, y2), gl64::mul(x3, y3))
}

/// `v mod p`, with the sign taken as in C++ (`fint`, `vf_common.h:424-427`).
pub const fn fint(v: i64) -> u64 {
    let r = if v < 0 { (v as u64).wrapping_neg() % FIELD_P } else { (v as u64) % FIELD_P };
    if v < 0 && r != 0 {
        FIELD_P - r
    } else {
        r
    }
}

// ---------------------------------------------------------------------------------------------
// Version admission (`vf_common.h:429-454`)
// ---------------------------------------------------------------------------------------------

/// `versionWordAdmitted` (`vf_common.h:430-432`): this build accepts one word only.
pub const fn version_word_admitted(v: u32) -> bool {
    v == PROGRAM_VERSION_WORD
}

/// `admitWord` (`vf_common.h:448-454`): the first admitted word sticks for the run; after that,
/// only that word is admitted. The C++ globals are `StageState.run_version_word` and
/// `run_version_word_fixed`.
pub fn admit_word(st: &mut StageState, v: u32) -> bool {
    if st.run_version_word_fixed {
        return v == st.run_version_word;
    }
    if !version_word_admitted(v) {
        return false;
    }
    st.run_version_word = v;
    st.run_version_word_fixed = true;
    true
}

// ---------------------------------------------------------------------------------------------
// tau (`vf_common.h:471-476`)
// ---------------------------------------------------------------------------------------------

/// `tauServed` (`vf_common.h:471-476`): a multiple of 32; `2^a` or `2^a + 2^b`; at most 256.
pub const fn tau_served(tau: u64) -> bool {
    if tau < 32 || tau > 256 || tau % 32 != 0 {
        return false;
    }
    let mut first = 32u64;
    while 2 * first <= tau {
        first *= 2;
    }
    let left = tau - first;
    left & left.wrapping_sub(1) == 0
}

// ---------------------------------------------------------------------------------------------
// Equality tables and round orders (`vf_common.h:919-962`)
// ---------------------------------------------------------------------------------------------

/// `eqTab` (`vf_common.h:919-938`): `t[c] = eq(z, c)` for all `c < 2^len`, with `z[0]` belonging
/// to the **top** bit of `c`. `z` must have at least `len` entries; `len < 64` is required for the
/// table to be addressable.
pub fn eq_tab(z: &[E], len: usize) -> Vec<E> {
    assert!(len < 64, "eq_tab: len must be below 64");
    assert!(z.len() >= len, "eq_tab: z has fewer entries than len");
    let mut t = Vec::with_capacity(1usize << len);
    t.push(E::one());
    for v in 0..len {
        let nt = t.len();
        let zv = z[v];
        // One buffer for the whole table. The level is filled from the back: the writes of
        // column `c` land at `2c` and `2c + 1`, both at or above `c`, so a descending walk still
        // reads the level's inputs. The output order matches the C++ loop (`d[2c]`, `d[2c+1]`).
        t.resize(2 * nt, E::zero());
        for c in (0..nt).rev() {
            let x = t[c];
            let hi = x * zv;
            t[2 * c] = x - hi;
            t[2 * c + 1] = hi;
        }
    }
    t
}

/// `eqOne` (`vf_common.h:941-949`): entry `c` of `eqTab(z, len)` without the table. `z[0]` again
/// belongs to the top bit. The C++ bounds check on `len` and `c` is `internal-eq-index`.
pub fn eq_one(z: &[E], len: i32, c: u64) -> Result<E> {
    if len < 0 || len > 63 || (c >> len) != 0 {
        return Err(Refusal::internal("internal-eq-index"));
    }
    let len = len as usize;
    assert!(z.len() >= len, "eq_one: z has fewer entries than len");
    let mut t = E::one();
    for v in 0..len {
        let hi = t * z[v];
        t = if (c >> (len - 1 - v)) & 1 != 0 { hi } else { t - hi };
    }
    Ok(t)
}

/// `orderDefault` (`vf_common.h:951-955`): `[mu - 1, ..., 0]`.
pub fn order_default(mu: usize) -> Vec<u32> {
    crate::iop::lkp::lkp_default_order(mu as u32)
}

/// `orderRange` (`vf_common.h:958-962`): `2, 1, 0, 5, 4, 3, 8, 7, 6,` then `mu - 1` down to 9.
/// The C++ precondition `mu >= 9` is checked by the shared implementation.
pub fn order_range(mu: usize) -> Vec<u32> {
    crate::iop::lkp::lkp_range_order(mu as u32, 0)
}

// ---------------------------------------------------------------------------------------------
// The standard parameter form and the acceptance policies (`vf_common.h:553-735`)
// ---------------------------------------------------------------------------------------------

/// `Served` (`vf_common.h:553-572`): conditions on the public inputs needed for YES or WITHIN
/// LIMITS. A field is true if the condition is met.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Served {
    pub experts: bool,
    pub five_limbs: bool,
    pub clamps: bool,
    pub prompt_source: bool,
    pub placement_table: bool,
    pub table_digests: bool,
    pub no_range_words: bool,
    pub three_bytes: bool,
    pub ring_degree: bool,
    pub one_shift: bool,
    pub one_placement: bool,
    pub softmax_table: bool,
    pub rotary_table: bool,
    pub norm_shifts: bool,
    pub two_codes: bool,
    pub next_token: bool,
    pub exact_match: bool,
    pub policy_named: bool,
}

/// `servedForm` (`vf_common.h:708-731`): the unmet conditions, comma-joined in the C++ order.
pub fn served_form(s: &Served) -> String {
    let clause: [(bool, &str); 18] = [
        (s.experts, "routed-experts"),
        (s.five_limbs, "five-limbs"),
        (s.clamps, "both-clamps"),
        (s.prompt_source, "prompt-source"),
        (s.placement_table, SERVED_LAYOUT),
        (s.table_digests, "table-digests"),
        (s.no_range_words, "no-range-words"),
        (s.three_bytes, "three-bytes"),
        (s.ring_degree, "ring-degree"),
        (s.one_shift, "one-shift"),
        (s.one_placement, "one-placement"),
        (s.softmax_table, "softmax-table"),
        (s.rotary_table, "rotary-table"),
        (s.norm_shifts, "norm-shifts (in KL.bin or in the lines MF and KF a norm's shift K is above its scale M and its output may be 0 for every input)"),
        (s.two_codes, SERVED_TWO_CODES),
        (s.next_token, "next-token (under -next-token the request must have r = T - 1 and e = T)"),
        (s.exact_match, SERVED_EXACT),
        (s.policy_named, SERVED_NAMED),
    ];
    let mut missed = String::new();
    for (met, name) in clause {
        if !met {
            if !missed.is_empty() {
                missed.push_str(", ");
            }
            missed.push_str(name);
        }
    }
    missed
}

/// `acceptancePolicyIsExactMatch` (`vf_common.h:615-617`).
pub const fn acceptance_policy_is_exact_match(c: u64, theta: u64, cap: u64, sh: u64, st: u64) -> bool {
    sh < 63 && c == theta && theta == (1u64 << sh) && cap == 0 && st.wrapping_add(4) == sh
}

/// `policyKind` (`vf_common.h:623-627`).
pub const fn policy_kind(c: u64, theta: u64, cap: u64, s: u64, sh: u64, st: u64) -> &'static str {
    if acceptance_policy_is_exact_match(c, theta, cap, sh, st) {
        "exact-match"
    } else if st.wrapping_add(4) == sh {
        "clipped-gap"
    } else if st == s {
        "log-probability"
    } else {
        "another-table"
    }
}

/// `aboveClip` (`vf_common.h:642-648`): an upper bound on how many of `n` checked tokens can have a
/// cost above `c`.
pub const fn above_clip(n: u64, c: u64, theta: u64, cap: u64, sh: u64) -> u64 {
    let least = if sh < 63 { 1u64 << sh } else { u64::MAX };
    let k = if cap < n { cap } else { n };
    if c <= least {
        return k;
    }
    let room = if theta > least {
        (n as u128) * ((theta - least) as u128) / ((c - least) as u128)
    } else {
        0
    };
    if room < k as u128 {
        room as u64
    } else {
        k
    }
}

/// `policyEmpty` (`vf_common.h:660-663`): nonzero if a result under the named policy would mean
/// nothing, by its numbers alone.
pub const fn policy_empty(n: u64, c: u64, theta: u64, cap: u64, sh: u64) -> i32 {
    let least = if sh < 63 { 1u64 << sh } else { u64::MAX };
    if c < least {
        1
    } else if theta < least {
        2
    } else if theta > c {
        3
    } else if theta == c && n != 0 && n <= cap {
        4
    } else {
        0
    }
}

/// `PolicyNamed` (`vf_common.h:674-682`): the caller's `-policy` option.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PolicyNamed {
    pub given: bool,
    pub kind: String,
    pub c: u64,
    pub theta: u64,
    pub cap: u64,
    pub s: u64,
    pub sh: u64,
}

impl PolicyNamed {
    /// `PolicyNamed::is` (`vf_common.h:678-681`): every number and the kind by equality.
    pub fn is(&self, f_c: u64, f_theta: u64, f_cap: u64, f_s: u64, f_sh: u64, f_st: u64) -> bool {
        self.kind == policy_kind(f_c, f_theta, f_cap, f_s, f_sh, f_st)
            && self.c == f_c
            && self.theta == f_theta
            && self.cap == f_cap
            && self.s == f_s
            && self.sh == f_sh
    }
}

/// `policyNamedRead` (`vf_common.h:688-704`): `<kind>,<C>,<theta>,<cap>,<s>,<sh>`; `None` is the
/// C++ `false` (the C++ function may have written some fields before it fails; the Rust caller
/// gets no partly filled value).
pub fn policy_named_read(text: &str) -> Option<PolicyNamed> {
    let comma = text.find(',')?;
    let kind = &text[..comma];
    if kind != "exact-match" && kind != "clipped-gap" {
        return None;
    }
    let b = text.as_bytes();
    let mut i = comma + 1;
    let mut vals = [0u64; 5];
    for (k, slot) in vals.iter_mut().enumerate() {
        let first = i;
        while i < b.len() && b[i].is_ascii_digit() {
            // Wrapping, as C++'s unsigned arithmetic: a run of more than 10 digits is rejected
            // below, after it has been consumed.
            *slot = slot.wrapping_mul(10).wrapping_add((b[i] - b'0') as u64);
            i += 1;
        }
        if i == first || i - first > 10 || (b[first] == b'0' && i - first > 1) {
            return None;
        }
        if k < 4 {
            if i >= b.len() || b[i] != b',' {
                return None;
            }
            i += 1;
        } else if i != b.len() {
            return None;
        }
    }
    Some(PolicyNamed {
        given: true,
        kind: String::from(kind),
        c: vals[0],
        theta: vals[1],
        cap: vals[2],
        s: vals[3],
        sh: vals[4],
    })
}

/// `rotaryServed` (`vf_common.h:705-707`).
pub const fn rotary_served(theta0: u64, dh: u64, lt: u64) -> bool {
    (theta0 == 10000 || theta0 == 500000) && dh <= 128 && lt <= 10
}

/// `goodEnding` (`vf_common.h:735`): the run may be accepted only if no cause applies.
pub const fn good_ending(below_bar: bool, not_served: bool) -> bool {
    !TEST_BUILD && !below_bar && !not_served
}

// ---------------------------------------------------------------------------------------------
// A lookup call (`vf_common.h:964-978`)
// ---------------------------------------------------------------------------------------------

/// `Call` (`vf_common.h:964-978`): one lookup call of the parameter file, consumed by
/// `vf_lookup_argument.h` and the sub-proofs. The C++ names that Rust keywords take are `func`
/// (`fn`) and `public` (`pub`); `z`, `y0`, `zb`, `vk` and `vb` are kept for layout fidelity even
/// though C++ does not read them (`[L:2315e951af98]`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Call {
    pub name: String,
    pub n: i32,
    pub iota: i32,
    pub k: i32,
    pub kappa: i32,
    pub func: i32,
    /// The table row that padding keys point to.
    pub t0: u64,
    pub tau: Option<Vec<u64>>,
    pub public: Vec<u64>,
    /// Per identity, rows with separate counts ("heavy rows"): pairs (row, count); or none.
    pub heavy: Vec<Vec<(u64, u64)>>,
    pub alpha: E,
    pub z: Vec<E>,
    pub y0: Vec<E>,
    pub zk: Vec<E>,
    pub zb: [Vec<E>; 2],
    pub vk: E,
    pub vb: [E; 2],
}

impl Call {
    /// `Call::K()`: `1 << kappa`.
    pub const fn k_count(&self) -> u64 {
        1u64 << self.kappa
    }

    /// `Call::I()`: `1 << iota`.
    pub const fn i_count(&self) -> u64 {
        1u64 << self.iota
    }

    /// `Call::tauAt(t)`: the row value, or `t` itself if the call has no `tau` vector.
    pub fn tau_at(&self, t: u64) -> u64 {
        match &self.tau {
            Some(tau) => tau[t as usize],
            None => t,
        }
    }
}
