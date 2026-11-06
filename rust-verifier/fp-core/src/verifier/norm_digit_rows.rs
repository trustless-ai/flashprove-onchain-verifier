//! Digit rows of the model's norms, ported from `verifier/src/vf_norm_digit_rows.h`.
//!
//! Limbs of a stream value: 4, or 5 with the line `xl 5` (`StageState::residual_stream_limbs`).
//! The five-limb row and its eight other equations are here; the layer and output-head sub-proofs
//! claim them. Nothing here checks anything.

use crate::field::ext::E;
use crate::verifier::engine::Aff;

/// Counts per instance: one norm of one layer, or the final norm.
pub fn led_ns(limbs: i32) -> i32 {
    2 * limbs - 1
}

/// Digits of a row.
pub fn led_nr(limbs: i32) -> i32 {
    if limbs == 5 {
        99
    } else {
        74
    }
}

/// Hidden products, sent before their weights.
pub fn led_np(limbs: i32) -> i32 {
    if limbs == 5 {
        7
    } else {
        3
    }
}

/// End values of the products' sumcheck.
pub fn led_no(limbs: i32) -> i32 {
    if limbs == 5 {
        4
    } else {
        3
    }
}

/// Equations after the carry equations.
pub fn led_lines(limbs: i32) -> i32 {
    if limbs == 5 {
        8
    } else {
        5
    }
}

/// The multiplier `mu` of digit `idx` in the row's range check (`ledMu4`).
pub fn led_mu4(idx: i32) -> u64 {
    match idx {
        7 => 32,
        44 => 2,
        45 => 128,
        48 => 4,
        _ => 1,
    }
}

/// `ledMu5`.
pub fn led_mu5(idx: i32) -> u64 {
    match idx {
        9 => 4,
        58 => 2,
        59 => 128,
        63 => 2,
        76 => 2,
        79 => 32,
        _ => 1,
    }
}

/// `ledMu`.
pub fn led_mu(idx: i32, limbs: i32) -> u64 {
    if limbs == 5 {
        led_mu5(idx)
    } else {
        led_mu4(idx)
    }
}

/// The output head's row has `LEDNE` more digits after the final norm's.
pub const LEDNE: usize = 21;
/// `EXC`: cells of the exponential-table slack.
pub const EXC: usize = 3;
/// `LEDG`: offset after the norm's digits, and length, of c, b, u, k, z, zs.
pub const LEDG: [[usize; 2]; 6] = [[0, 5], [5, 1], [6, 5], [11, 5], [16, 2], [18, EXC]];
/// `BIGH`.
pub const BIGH: u64 = 1u64 << 37;

/// `ledNRH`.
pub fn led_nrh(limbs: i32) -> i32 {
    led_nr(limbs) + LEDNE as i32
}

/// The constants that `LedK<T>` lifts into `T`: zero, one, and the canonical base-field scalar.
pub trait LedKind:
    Clone + core::ops::Add<Output = Self> + core::ops::Sub<Output = Self> + core::ops::Mul<E, Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
    fn from_e(x: E) -> Self;
}

impl LedKind for E {
    fn zero() -> Self {
        E::zero()
    }
    fn one() -> Self {
        E::one()
    }
    fn from_e(x: E) -> Self {
        x
    }
}

impl LedKind for Aff {
    fn zero() -> Self {
        Aff::default()
    }
    fn one() -> Self {
        Aff::constant(E::one())
    }
    fn from_e(x: E) -> Self {
        Aff::constant(x)
    }
}

/// `eI(v)` as a field element (the C++ `eB(fint(v))`).
fn ei(v: i64) -> E {
    E::from_base(crate::field::ext::F::from_u64(crate::verifier::common::fint(v)))
}

/// The five-limb row (`struct Row5<T>`): its 99 digits (`cell + 128`) and the numbers they form.
pub struct Row5<T> {
    pub dg: [T; 99],
    pub c: [T; 10],
    pub vlo: T,
    pub vhi: T,
    pub a: T,
    pub b: T,
    pub sig: T,
    pub s0: T,
    pub l1: T,
    pub h1: T,
    pub blo: T,
    pub bhi: T,
    pub kap: T,
    pub rlo: T,
    pub rhi: T,
    pub r: T,
    pub q1: T,
    pub rr: T,
    pub rq: T,
}

/// `row5(cell)`: the row's cell `j` as a `T`.
pub fn row5<T: LedKind, F: Fn(usize) -> T>(cell: F) -> Row5<T> {
    let mut r = Row5 {
        dg: core::array::from_fn(|_| T::zero()),
        c: core::array::from_fn(|_| T::zero()),
        vlo: T::zero(),
        vhi: T::zero(),
        a: T::zero(),
        b: T::zero(),
        sig: T::zero(),
        s0: T::zero(),
        l1: T::zero(),
        h1: T::zero(),
        blo: T::zero(),
        bhi: T::zero(),
        kap: T::zero(),
        rlo: T::zero(),
        rhi: T::zero(),
        r: T::zero(),
        q1: T::zero(),
        rr: T::zero(),
        rq: T::zero(),
    };
    for j in 0..99 {
        r.dg[j] = cell(j) + T::from_e(ei(128));
    }
    r.vlo = dig(&r, 0, 6);
    r.vhi = dig(&r, 6, 4);
    r.c[0] = T::zero();
    for s in 1..=8 {
        r.c[s] = dig(&r, 10 + 6 * (s - 1), 6) - T::from_e(ei(1i64 << 47));
    }
    r.c[9] = r.dg[9].clone();
    r.s0 = r.dg[59].clone();
    r.a = r.dg[58].clone() * ei(2)
        + r.dg[59].clone()
        + r.dg[60].clone() * ei(256)
        + r.dg[61].clone() * ei(65536);
    r.b = r.dg[62].clone() + r.dg[63].clone() * ei(256);
    r.sig = r.a.clone() + r.b.clone() * ei(1 << 24);
    r.l1 = dig(&r, 64, 5);
    r.h1 = dig(&r, 69, 5);
    r.blo = dig(&r, 74, 3);
    r.bhi = dig(&r, 77, 2);
    r.kap = r.dg[79].clone() - T::from_e(ei(4));
    r.rlo = dig(&r, 80, 3);
    r.rhi = dig(&r, 83, 3);
    r.r = r.rlo.clone() + r.rhi.clone() * ei(1 << 24);
    r.q1 = dig(&r, 86, 3);
    r.rr = dig(&r, 89, 5);
    r.rq = dig(&r, 94, 5);
    r
}

/// `dig(at, n)`: `sum_j 256^j Dg[at + j]`.
fn dig<T: LedKind>(r: &Row5<T>, at: usize, n: usize) -> T {
    let mut s = T::zero();
    let mut sc = 1i64;
    for j in 0..n {
        s = s + r.dg[at + j].clone() * ei(sc);
        sc *= 256;
    }
    s
}

/// `ledCarry5`: `W_s + c_s - v_s - 256 c_(s+1)`.
pub fn led_carry5<T: LedKind>(r: &Row5<T>, s: usize, ws: &T) -> T {
    ws.clone() + r.c[s].clone() - r.dg[s].clone() - r.c[s + 1].clone() * ei(256)
}

/// `ledLines5`: the eight other equations, as differences that must be 0.
pub fn led_lines5<T: LedKind>(r: &Row5<T>, p: &[T; 7], eps: E, two: &T, out: &mut [T; 8]) {
    out[0] = p[1].clone() - r.blo.clone() - r.bhi.clone() * ei(1 << 23);
    out[1] = r.vlo.clone() + T::from_e(eps) - p[0].clone() - r.blo.clone() * ei(1 << 25)
        - r.l1.clone()
        + r.kap.clone() * ei(1i64 << 48);
    out[2] = r.vhi.clone() - r.bhi.clone() - p[2].clone() - r.kap.clone();
    out[3] = r.l1.clone() + r.h1.clone() - r.sig.clone() * ei(2);
    out[4] = p[4].clone() + p[5].clone() - r.q1.clone();
    out[5] = p[6].clone();
    out[6] = two.clone() + r.sig.clone() - r.s0.clone() - p[3].clone() * ei(2)
        - r.q1.clone() * ei(1 << 25)
        - r.rr.clone() * ei(2);
    out[7] = r.rr.clone() + r.rq.clone() - r.sig.clone() + T::one();
}

/// `ledProducts5`: `sum om[j] P_j`, the `P_j` formed from the sumcheck's end values.
pub fn led_products5(om: &[E], a: E, b: E, lo: E, hi: E) -> E {
    om[0] * a * a
        + om[1] * a * b
        + om[2] * b * b
        + om[3] * lo * a
        + om[4] * lo * b
        + om[5] * hi * a
        + om[6] * hi * b
}
