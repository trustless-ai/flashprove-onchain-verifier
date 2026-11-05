//! The verifier's four public tables and the gate on their digests.
//!
//! Ported from `verifier/src/cp_verify.cpp`:
//!   - `sigmoidTableEntry`, `sigmoidClampTableEntry` and `gateTableEntry` (lines 181-215), with the
//!     parameter-file lines `eg`, `smax` and `gcl` (186, 193);
//!   - the table lists and digests (1412-1428, 1592-1610, 2004-2011) and the digest gate `tblHeld`
//!     (1301-1303);
//! and from `verifier/src/vf_attention_shape.h` (the softmax list, lines 203-212).
//!
//! The C++ functions read file-scope variables (`gateTableInputFractionBits`, `SMAX`, `GCL`);
//! here those values are fields of [`TableParams`]. The tables are made with the platform's
//! floating-point library. [`libm`]'s `exp`, `sin`, `cos`, `pow` and `rint` can differ from a
//! platform's by one unit in the last place, so the tables are not fixed bit for bit by this
//! module: what fixes them is the parameter file's 32 digest lines, which
//! [`check_table_digests`] compares. For a policy whose lines are present, the comparison is on
//! every integer entry's digest, so a last-bit difference that changed an integer would be seen.
//!
//! `round` rounds halves away from zero (C's `round`); `rint` rounds halves to even, which is
//! `nearbyint` under the default rounding mode (C's `nearbyint`; the port uses `libm::rint`).

use alloc::vec::Vec;

use crate::hash::calls::HashCalls;
use crate::hash::earlier::{earlier_hash_h_digest, DW};

/// The number of entries of table SILU and of table SIG: keys are 16-bit (`cp_verify.cpp:1414`).
pub const TABLE_ENTRIES: usize = 65536;

/// `SMAXTOP`: the largest absolute value in table SILU (`vf_widths_and_bounds.h:40`).
pub const SMAXTOP: i32 = 4095;

/// The number of 32-bit words of the digest lines of the four tables (`TBLW`, `vf_widths_and_bounds.h:25`).
pub const TBLW: usize = 4 * DW;

/// The table inputs that the C++ program holds in file-scope variables or derives from the
/// parameter file. `Default` gives the C++ initial values (`cp_verify.cpp:185-193`); `theta0`,
/// `cs`, `dh`, `lt`, `s` and `rx` have no default and come from the parameter file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableParams {
    /// The line `eg`: the input of table SILU is shifted by this many fractional bits (default 8).
    pub eg: u32,
    /// The line `smax`: table SILU's values are clamped to `[-smax, smax]` (default 4095).
    pub smax: i32,
    /// The line `gcl 1`: table SIG clamps the gating value (default off).
    pub gcl: bool,
    /// `theta0_lo + 2^32 theta0_hi`, the RoPE table's base.
    pub theta0: u64,
    /// The line `cs`: the RoPE table's scale is `2^cs`.
    pub cs: u32,
    /// The line `dh`: a head's width; the RoPE table has `dh / 2` pairs.
    pub dh: u64,
    /// The line `lt`: the RoPE table has `2^lt` positions.
    pub lt: u32,
    /// The line `S`: the softmax table's scale is `2^S`.
    pub s: u32,
    /// The line `rx`: the softmax table's step is `2^-rx`.
    pub rx: u32,
}

impl Default for TableParams {
    fn default() -> Self {
        Self {
            eg: 8,
            smax: SMAXTOP,
            gcl: false,
            theta0: 0,
            cs: 0,
            dh: 0,
            lt: 0,
            s: 0,
            rx: 0,
        }
    }
}

/// C's `(int)round(x)` for a value in `i32`'s range.
fn round_i32(x: f64) -> i32 {
    libm::round(x) as i32
}

/// Table SIG at key `t` (`sigmoidTableEntry`, `cp_verify.cpp:181-184`): 16 times 4096 / (1 + e^-z),
/// with `z = (t - 32768) / 256`.
pub fn sigmoid_table_entry(t: i32) -> i32 {
    let z = (t - 32768) as f64 / 256.0;
    16 * round_i32(4096.0 / (1.0 + libm::exp(-z)))
}

/// Table SIG at key `t` as the verifier forms it (`sigmoidClampTableEntry`, `cp_verify.cpp:205-210`):
/// the sigmoid itself without `gcl`; with it, the sigmoid at `t + 16384` below 32768 and a clamped
/// linear entry from there on.
pub fn sigmoid_clamp_table_entry(p: &TableParams, t: i32) -> i32 {
    if !p.gcl {
        return sigmoid_table_entry(t);
    }
    if t < 32768 {
        return sigmoid_table_entry(t + 16384);
    }
    let c = t - 49152;
    let c = if c < -127 {
        -127
    } else if c > 127 {
        127
    } else {
        c
    };
    c + 128
}

/// Table SILU at key `t` before the 4096 is added (`gateTableEntry`, `cp_verify.cpp:197-204`).
///
/// The input is `c / 2^eg` with `c = t - 32768` clamped to `[-64 2^eg, 64 2^eg - 1]`; the value is
/// `round(64 c / 2^eg / (1 + e^-c/2^eg))`, clamped to `[-smax, smax]`. `eg` is 4 to 7 for every
/// valid parameter file (`cp_verify.cpp:1065`), so `64 << eg` does not overflow.
pub fn gate_table_entry(p: &TableParams, t: i32) -> i32 {
    let top = 64i32 << p.eg;
    let mut c = t - 32768;
    if c < -top {
        c = -top;
    }
    if c > top - 1 {
        c = top - 1;
    }
    let z = c as f64 / (1u32 << p.eg) as f64;
    let v = round_i32(64.0 * (z / (1.0 + libm::exp(-z))));
    if v < -p.smax {
        -p.smax
    } else if v > p.smax {
        p.smax
    } else {
        v
    }
}

/// Table SILU (`cp_verify.cpp:1413-1414`): 65,536 words, `gate_table_entry(t) + 4096` at key `t`.
pub fn silu_table(p: &TableParams) -> Vec<u32> {
    (0..TABLE_ENTRIES)
        .map(|t| (gate_table_entry(p, t as i32) + 4096) as u32)
        .collect()
}

/// Table SIG (`cp_verify.cpp:1423`): 65,536 words when the model has experts (the line `NE` is not
/// zero), and no table at all otherwise (`cp_verify.cpp:1420-1426`, `1192-1194`).
pub fn sigmoid_table(p: &TableParams, has_experts: bool) -> Option<Vec<u32>> {
    if !has_experts {
        return None;
    }
    Some(
        (0..TABLE_ENTRIES)
            .map(|t| sigmoid_clamp_table_entry(p, t as i32) as u32)
            .collect(),
    )
}

/// The RoPE table (`cp_verify.cpp:1592-1609`): first the cosines and then the sines, for t = 0 to
/// `t_positions - 1` and within t for i = 0 to `dh / 2 - 1`. The entry is
/// `4096 + round(2^cs f(t theta0^(-2 i / dh)))`, f the cosine or the sine.
pub fn rope_table(theta0: u64, cs: u32, dh: u64, t_positions: u64) -> Vec<u32> {
    let mut w = Vec::with_capacity(2 * t_positions as usize * (dh / 2) as usize);
    for sine in 0..2 {
        for t in 0..t_positions {
            for i in 0..dh / 2 {
                let ang = (t as f64) * libm::pow(theta0 as f64, -2.0 * (i as f64) / (dh as f64));
                let f: f64 = if sine == 0 {
                    libm::cos(ang)
                } else {
                    libm::sin(ang)
                };
                let e = libm::round((1u32 << cs) as f64 * f) as i64;
                w.push((e + 4096) as u32);
            }
        }
    }
    w
}

/// The softmax table (`vf_attention_shape.h:203-212`): `Tt[u] = nearbyint(2^s exp(-u / 2^rx))` for
/// u = 0, 1, .. until the first u at which it is 0; `u0` is that u and `Tt` has `u0` entries.
pub fn exp_table(s: u32, rx: u32) -> (Vec<u64>, u64) {
    let mut tt = Vec::new();
    let mut u = 0u64;
    loop {
        let v = libm::rint(libm::ldexp(1.0, s as i32) * libm::exp(-(u as f64) / libm::ldexp(1.0, rx as i32)));
        if v == 0.0 {
            return (tt, u);
        }
        tt.push(v as u64);
        u += 1;
    }
}

/// `K(72; words)`: the digest of one public table (`cp_verify.cpp:1416`, `1424`, `1607`, `2008`).
pub fn table_digest(words: &[u32], calls: &mut HashCalls) -> [u32; DW] {
    let mut out = [0u32; DW];
    earlier_hash_h_digest(&mut out, 72, words, words.len() as u64, 1, calls);
    out
}

/// The model facts that the four tables need but that are not optional parameter-file lines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableFacts {
    /// The line `lt`: the RoPE table has `2^lt` positions.
    pub lt: u32,
    /// The line `dh`.
    pub dh: u64,
    /// `theta0_lo + 2^32 theta0_hi`.
    pub theta0: u64,
    /// The line `cs`.
    pub cs: u32,
    /// The line `S`.
    pub s: u32,
    /// The line `rx`.
    pub rx: u32,
    /// The line `NE` is not zero: the model has experts, so table SIG exists.
    pub has_experts: bool,
}

/// Reads one `name value` line strictly, as `polScan` accepts it (`wordLineForm`, `vf_common.h:190-205`):
/// exactly one space, a decimal value of at most ten digits without a leading zero, no other bytes.
fn split_word_line(line: &[u8]) -> Option<(&[u8], u32)> {
    let sp = line.iter().position(|&c| c == b' ')?;
    let (name, value) = (&line[..sp], &line[sp + 1..]);
    if name.is_empty() || value.is_empty() || value.len() > 10 {
        return None;
    }
    if value.len() > 1 && value[0] == b'0' {
        return None;
    }
    let mut x = 0u32;
    for &c in value {
        if !c.is_ascii_digit() {
            return None;
        }
        x = x.checked_mul(10)?.checked_add((c - b'0') as u32)?;
    }
    Some((name, x))
}

/// Reads the optional lines `eg`, `smax` and `gcl` of a parameter file's tail into `p`. A repeated
/// line is ignored; the strict scan owns the order and the spelling, so a line that is malformed
/// here is left to it (`cp_verify.cpp:1057-1088`).
fn read_optional_lines(policy_rest: &[u8], p: &mut TableParams) {
    let mut eg_seen = false;
    let mut smax_seen = false;
    let mut gcl_seen = false;
    for line in policy_rest.split(|&c| c == b'\n') {
        let Some((name, value)) = split_word_line(line) else {
            continue;
        };
        match name {
            b"eg" if !eg_seen && (4..=7).contains(&value) => {
                p.eg = value;
                eg_seen = true;
            }
            b"smax" if !smax_seen && matches!(value, 2047 | 1023 | 511 | 255) => {
                p.smax = value as i32;
                smax_seen = true;
            }
            b"gcl" if !gcl_seen && value == 1 => {
                p.gcl = true;
                gcl_seen = true;
            }
            _ => {}
        }
    }
}

/// The digest gate (`tblHeld`, `cp_verify.cpp:1301-1303`): if the parameter file's tail carries all
/// 32 lines `tsilu0` .. `texp7`, build the four tables and compare each digest with its line.
///
/// Returns `Err` with the name the C++ program prints:
///   - `policy-tables`: the lines are absent and incomplete, interrupted or out of order
///     (`cp_verify.cpp:1109-1116`, `1165`), or they are present on a model without experts
///     (`cp_verify.cpp:1194`);
///   - `table-digest-silu`, `table-digest-sigmoid`, `table-digest-rope`, `table-digest-exp`: the
///     corresponding table's digest differs from its eight lines.
///
/// With no digest lines at all the gate does nothing, as `tblHeld` does (`tblAt == 0`).
pub fn check_table_digests(policy_rest: &[u8], facts: &TableFacts) -> Result<(), &'static str> {
    const NAMES: [&[u8]; 4] = [b"tsilu", b"tsig", b"trope", b"texp"];
    let mut p = TableParams {
        theta0: facts.theta0,
        cs: facts.cs,
        dh: facts.dh,
        lt: facts.lt,
        s: facts.s,
        rx: facts.rx,
        ..TableParams::default()
    };
    read_optional_lines(policy_rest, &mut p);
    let mut tbl = [[0u32; DW]; 4];
    let mut tbl_at = 0usize;
    let mut prev_table = false;
    let mut saw_call = false;
    for line in policy_rest.split(|&c| c == b'\n') {
        let is_table = NAMES.iter().any(|n| line.starts_with(n));
        if is_table {
            // The lines are consecutive and in the order tsilu0 .. texp7, and no call line precedes
            // them (`cp_verify.cpp:1109-1113`).
            if tbl_at >= TBLW || (tbl_at != 0 && !prev_table) || saw_call {
                return Err("policy-tables");
            }
            let Some((name, value)) = split_word_line(line) else {
                return Err("policy-tables");
            };
            let want = alloc::format!("{}{}", core::str::from_utf8(NAMES[tbl_at / DW]).unwrap(), tbl_at % DW);
            if name != want.as_bytes() {
                return Err("policy-tables");
            }
            tbl[tbl_at / DW][tbl_at % DW] = value;
            tbl_at += 1;
            prev_table = true;
        } else {
            prev_table = false;
            // A line `call`, `callA` or `callH` precedes no digest line (`cp_verify.cpp:1109-1110`).
            if line.starts_with(b"call") {
                saw_call = true;
            }
        }
    }
    if tbl_at == 0 {
        return Ok(());
    }
    if tbl_at != TBLW {
        return Err("policy-tables");
    }
    // The lines are accepted only if all four tables are formed, which needs experts
    // (`cp_verify.cpp:1192-1194`).
    if !facts.has_experts {
        return Err("policy-tables");
    }
    let mut calls = HashCalls::new();
    if table_digest(&silu_table(&p), &mut calls) != tbl[0] {
        return Err("table-digest-silu");
    }
    let sig = sigmoid_table(&p, true).expect("the model has experts");
    if table_digest(&sig, &mut calls) != tbl[1] {
        return Err("table-digest-sigmoid");
    }
    if table_digest(&rope_table(p.theta0, p.cs, p.dh, 1u64 << p.lt), &mut calls) != tbl[2] {
        return Err("table-digest-rope");
    }
    let (tt, u0) = exp_table(p.s, p.rx);
    let words: Vec<u32> = tt[..u0 as usize].iter().map(|&x| x as u32).collect();
    if table_digest(&words, &mut calls) != tbl[3] {
        return Err("table-digest-exp");
    }
    Ok(())
}
