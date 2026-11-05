//! Code sizes and round-error formulas, ported from `blocks/numbers/codes.h`.

use alloc::string::String;
use core::cmp::Ordering;

use super::real::{surely_lt, Big, Bound, Dir, Real};
use super::setting::{CountSource, Setting};

/// The least `l` with `2^l >= v` (`ceil_log2`).
pub fn ceil_log2(v: u64) -> u32 {
    if v <= 1 {
        0
    } else {
        64 - (v - 1).leading_zeros()
    }
}

/// A code's public sizes (`CodeSize`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodeSize {
    pub name: String,
    pub log_n: u32,
    pub ell: u64,
    pub r: u64,
    pub over_e: bool,
}

impl Default for CodeSize {
    /// The members' default member initializers (`CodeSize`, codes.h:47-52).
    fn default() -> Self {
        CodeSize {
            name: String::new(),
            log_n: 0,
            ell: 0,
            r: 0,
            over_e: false,
        }
    }
}

impl CodeSize {
    pub fn n(&self) -> u64 {
        1u64 << self.log_n
    }
    pub fn coordinates(&self) -> u64 {
        self.ell + self.r
    }
    pub fn dim(&self, s: &Setting) -> u64 {
        if !s.circle || self.r == 0 {
            return self.ell + self.r;
        }
        let step = 1u64 << ceil_log2(self.r);
        (self.ell + step - 1) / step * step + self.r
    }
    pub fn k(&self, s: &Setting) -> u64 {
        if s.circle {
            self.dim(s)
        } else {
            self.dim(s) - 1
        }
    }
}

/// At how many distinct positions a row's symbols are uniform (`hidden_positions`).
pub fn hidden_positions(s: &Setting, c: &CodeSize) -> u64 {
    if s.circle && c.r != 0 && c.r % 2 == 0 {
        c.r - 1
    } else {
        c.r
    }
}

/// How many random coordinates hide `t` positions (`tail_for`).
pub fn tail_for(s: &Setting, t: u64) -> u64 {
    if s.circle && t != 0 && t % 2 == 0 {
        t + 1
    } else {
        t
    }
}

#[inline]
pub fn name_of_source(s: CountSource) -> &'static str {
    match s {
        CountSource::Third => "within a third of the distance",
        CountSource::Johnson => "Johnson",
    }
}

#[inline]
pub fn rests_on(s: CountSource) -> &'static str {
    match s {
        CountSource::Third => {
            "a lemma of the paper that this protocol builds on (see THIRD_PARTY.md), proved there"
        }
        CountSource::Johnson => {
            "the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given"
        }
    }
}

/// How a group takes its distance (`Radius`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Radius {
    Johnson,
    At,
}

#[inline]
pub fn name_of_radius(r: Radius) -> &'static str {
    match r {
        Radius::Johnson => "Johnson radius with slack",
        Radius::At => "a distance of its own",
    }
}

/// A code at one relative distance (`Proximity`).
#[derive(Clone, Debug)]
pub struct Proximity {
    pub agree: Bound,
    pub delta: Bound,
    pub eta: Bound,
    pub m: u64,
    pub from_m: bool,
    pub source: CountSource,
    pub count: Bound,
    pub list: Big,
}

impl Default for Proximity {
    fn default() -> Self {
        Proximity {
            agree: Bound::failed(),
            delta: Bound::failed(),
            eta: Bound::default(),
            m: 0,
            from_m: false,
            source: CountSource::Johnson,
            count: Bound::failed(),
            list: Big::from_u64(1),
        }
    }
}

impl Proximity {
    pub fn bad(&self) -> bool {
        self.agree.bad || self.delta.bad || self.count.bad
    }
}

/// A code as the formulas read it (`Word`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Word {
    pub log_n: u32,
    pub k_: u64,
}

impl Word {
    pub fn n(&self) -> u64 {
        1u64 << self.log_n
    }
    pub fn k(&self) -> u64 {
        self.k_
    }
}

pub fn word_of(s: &Setting, c: &CodeSize) -> Word {
    Word { log_n: c.log_n, k_: c.k(s) }
}

pub fn repeated(s: &Setting, c: &CodeSize, log_n: u32) -> Word {
    if log_n <= c.log_n {
        word_of(s, c)
    } else {
        Word { log_n, k_: c.k(s) << (log_n - c.log_n) }
    }
}

pub fn rho_of(c: &Word) -> Bound {
    Bound::ratio(&Big::from_u64(c.k()), &Big::from_u64(c.n()))
}

pub fn rho_of_code(s: &Setting, c: &CodeSize) -> Bound {
    rho_of(&word_of(s, c))
}

/// The counting form of the Johnson bound (`johnson_list`).
pub fn johnson_list(agree: &Bound, lambda: &Bound, bad: &mut bool) -> Big {
    let l = (agree.clone() - lambda.clone())
        / (agree.clone() * agree.clone() - lambda.clone());
    *bad = *bad || l.bad;
    if l.bad {
        Big::from_u64(1)
    } else {
        l.hi.floor()
    }
}

/// The count of `CountSource::Johnson` (`johnson_count`).
pub fn johnson_count(c: &Word, rho: &Bound, delta: &Bound, m: u64) -> Bound {
    let big_m = Bound::ratio(
        &Big::add(&Big::mul(&Big::from_u64(2), &Big::from_u64(m)), &Big::from_u64(1)),
        &Big::from_u64(2),
    );
    let root = Bound::sqrt(rho);
    (Bound::from_u64(2) * Bound::pow(&big_m, 5)
        + Bound::from_u64(3) * big_m.clone() * delta.clone() * rho.clone())
        / (Bound::from_u64(3) * rho.clone() * root.clone())
        * Bound::from_big(&Big::from_u64(c.n()))
        + big_m / root
}

/// The code at the distance that `m` gives (`johnson`).
pub fn johnson(c: &Word, m: u64) -> Proximity {
    let rho = rho_of(c);
    let root = Bound::sqrt(&rho);
    let mut x = Proximity {
        m,
        from_m: true,
        source: CountSource::Johnson,
        ..Proximity::default()
    };
    x.eta = root.clone() / Bound::from_big(&Big::from_u64(m));
    x.agree = root + x.eta.clone();
    x.delta = Bound::from_u64(1) - x.agree.clone();
    x.count = johnson_count(c, &rho, &x.delta, m);
    let mut bad = m < 3 || c.k() >= c.n();
    x.list = johnson_list(&x.agree, &rho, &mut bad);
    if bad {
        x.count = Bound::failed();
    }
    x
}

pub fn johnson_code(s: &Setting, c: &CodeSize, m: u64) -> Proximity {
    johnson(&word_of(s, c), m)
}

/// The code at the distance `1 - agree`, with the first source that applies (`at_distance`).
pub fn at_distance(c: &Word, agree: &Bound) -> Proximity {
    let mut x = Proximity::default();
    if agree.bad || c.k() >= c.n() {
        return x;
    }
    let n = Bound::from_big(&Big::from_u64(c.n()));
    let d = Bound::from_big(&Big::from_u64(c.n() - c.k()));
    let rho = rho_of(c);
    x.agree = agree.clone();
    x.delta = Bound::from_u64(1) - agree.clone();
    if x.delta.bad {
        x.count = Bound::failed();
        return x;
    }
    let errors = (x.delta.clone() * n.clone()).hi.floor();
    if Big::cmp(&Big::mul(&Big::from_u64(3), &errors), &Big::from_u64(c.n() - c.k()))
        == Ordering::Less
    {
        x.source = CountSource::Third;
        x.count = Bound::from_big(&Big::add(&errors, &Big::from_u64(1)));
    } else {
        let root = Bound::sqrt(&rho);
        x.source = CountSource::Johnson;
        x.eta = agree.clone() - root.clone();
        let q = root / x.eta.clone();
        if q.bad || !q.hi.ceil().fits_u64() {
            x.count = Bound::failed();
            return x;
        }
        x.m = core::cmp::max(q.hi.ceil().to_u64(), 3);
        x.count = johnson_count(c, &rho, &x.delta, x.m);
        let mut bad = false;
        if !surely_lt(
            &(Bound::from_u64(2) * x.delta.clone() * n),
            &d,
        ) {
            x.list = johnson_list(agree, &rho, &mut bad);
        }
        if bad {
            x.count = Bound::failed();
        }
    }
    x
}

pub fn at_distance_code(s: &Setting, c: &CodeSize, agree: &Bound) -> Proximity {
    at_distance(&word_of(s, c), agree)
}

/// The error of mutual correlated agreement (`mca_error`).
pub fn mca_error(s: &Setting, x: &Proximity) -> Bound {
    let mut a = x.count.clone();
    if s.circle && x.source != CountSource::Third {
        a = a + Bound::from_big(&x.list);
    }
    a / Bound::from_big(&s.card_e())
}

/// The smallest `t` with `factor (agree^t + extra) <= 2^-bits` (`positions`).
pub fn positions(agree: &Bound, bits: u32, extra: &Bound, factor: u64) -> u64 {
    if factor == 0 {
        return 0;
    }
    let num = Real::two_to(-(bits as i64));
    let den = Real::from_u64(factor);
    let goal = Real::div(&num, &den, Dir::Down);
    if agree.bad || extra.bad || !(agree.hi < Real::from_u64(1)) || !(extra.hi < goal) {
        return 0;
    }
    let ok = |t: u64| {
        let pw = Real::pow(agree.hi.clone(), t, Dir::Up);
        Real::add(&pw, &extra.hi, Dir::Up) <= goal
    };
    let mut hi = 1u64;
    while !ok(hi) {
        hi *= 2;
        if hi > (1u64 << 32) {
            return 0;
        }
    }
    let mut lo = hi / 2;
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if ok(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    hi
}

/// An `m` in [3, limit] at which `good` is true, or 0 (`largest_m`).
pub fn largest_m<F: FnMut(u64) -> bool>(mut good: F, limit: u64) -> u64 {
    let mut lo = 3;
    while lo < 67 && !good(lo) {
        lo += 1;
    }
    if lo == 67 {
        return 0;
    }
    let mut hi = lo + 1;
    while hi < limit && good(hi) {
        lo = hi;
        hi *= 2;
    }
    if hi >= limit {
        if good(limit) {
            return limit;
        }
        hi = limit;
    }
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if good(mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn powers_error(s: &Setting, rows: u64) -> Bound {
    Bound::ratio(
        &Big::from_u64(if rows != 0 { rows - 1 } else { 0 }),
        &s.card_e(),
    )
}

pub fn field_error(s: &Setting, degree: u64) -> Bound {
    Bound::ratio(&Big::from_u64(degree), &s.card_e())
}

pub fn field_error_nonzero(s: &Setting, degree: u64) -> Bound {
    let e = s.card_e();
    Bound::ratio(
        &Big::from_u64(degree),
        &Big::sub(&e, &Big::from_u64(1)),
    )
}

pub fn sample_error(s: &Setting, list: &Big, cube_bits: u32, answers: u32) -> Bound {
    let base = if cube_bits >= 2 {
        field_error(s, cube_bits as u64)
    } else {
        field_error_nonzero(s, 1)
    };
    Bound::from_big(&Big::mul(list, list)) / Bound::from_u64(2) * Bound::pow(&base, answers as u64)
}

pub fn sample_error_default(s: &Setting, list: &Big, cube_bits: u32) -> Bound {
    sample_error(s, list, cube_bits, s.samples)
}
