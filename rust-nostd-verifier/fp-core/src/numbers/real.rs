//! Exact integer and dyadic-rational arithmetic, ported from `blocks/numbers/real.h`.
//!
//! `Big` is a non-negative integer of any size, exact. `Real` is `m * 2^e`; an operation that
//! cannot be exact takes a direction and is cut to about `REAL_BITS` bits. `Bound` is a pair of
//! Reals with a `bad` flag for formulas used outside their range. Decisions compare exact Reals at
//! the safe end; only printed figures use `f64`, through `libm`.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::ops::{Add, Mul, Sub};

/// `REAL_BITS` (`real.h`).
pub const REAL_BITS: usize = 192;
/// `DRAW_TRIES` (`blocks/base.h:62`).
pub const DRAW_TRIES: u32 = 6;
/// `NONZERO_TRIES` (`blocks/base.h:62`).
pub const NONZERO_TRIES: u32 = 2;

/// A non-negative integer of any size, little-endian 32-bit limbs with no top zero limb.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Big {
    pub w: Vec<u32>,
}

impl Big {
    pub fn zero() -> Self {
        Big { w: Vec::new() }
    }

    pub fn from_u64(x: u64) -> Self {
        let mut w = Vec::new();
        let mut x = x;
        while x != 0 {
            w.push(x as u32);
            x >>= 32;
        }
        Big { w }
    }

    pub fn is_zero(&self) -> bool {
        self.w.is_empty()
    }

    pub fn bits(&self) -> usize {
        if self.w.is_empty() {
            return 0;
        }
        32 * (self.w.len() - 1) + (32 - self.w[self.w.len() - 1].leading_zeros() as usize)
    }

    pub fn bit(&self, i: usize) -> bool {
        i / 32 < self.w.len() && ((self.w[i / 32] >> (i % 32)) & 1) != 0
    }

    /// Is any of the lowest `n` bits set?
    pub fn any_below(&self, n: usize) -> bool {
        for i in 0..self.w.len() {
            if 32 * i >= n {
                break;
            }
            let mut x = self.w[i];
            if n - 32 * i < 32 {
                x &= (1u32 << (n - 32 * i)) - 1;
            }
            if x != 0 {
                return true;
            }
        }
        false
    }

    pub fn fits_u64(&self) -> bool {
        self.w.len() <= 2
    }

    pub fn to_u64(&self) -> u64 {
        assert!(self.fits_u64(), "Big::to_u64: the number does not fit");
        (self.w.first().copied().unwrap_or(0) as u64)
            | ((self.w.get(1).copied().unwrap_or(0) as u64) << 32)
    }

    /// `Big::dec()` (`real.h:232-245`): the number in decimal digits.
    pub fn dec(&self) -> String {
        if self.is_zero() {
            return String::from("0");
        }
        let ten9 = Big::from_u64(1_000_000_000);
        let mut x = self.clone();
        let mut digits: Vec<u8> = Vec::new();
        while !x.is_zero() {
            let (q, r) = Big::divmod(&x, &ten9);
            let mut d = if r.is_zero() { 0 } else { r.to_u64() };
            let mut i = 0;
            while i < 9 && (!q.is_zero() || d != 0) {
                digits.push(b'0' + (d % 10) as u8);
                d /= 10;
                i += 1;
            }
            x = q;
        }
        digits.reverse();
        String::from_utf8(digits).expect("Big::dec: decimal digits are UTF-8")
    }

    pub fn cmp(a: &Big, b: &Big) -> Ordering {
        if a.w.len() != b.w.len() {
            return a.w.len().cmp(&b.w.len());
        }
        for i in (0..a.w.len()).rev() {
            if a.w[i] != b.w[i] {
                return a.w[i].cmp(&b.w[i]);
            }
        }
        Ordering::Equal
    }

    pub fn two_to(n: usize) -> Self {
        Big::from_u64(1).shl(n)
    }

    pub fn shl(&self, n: usize) -> Self {
        if self.w.is_empty() || n == 0 {
            return self.clone();
        }
        let q = n / 32;
        let s = n % 32;
        let mut r = vec![0u32; self.w.len() + q + 1];
        for i in 0..self.w.len() {
            let x = (self.w[i] as u64) << s;
            r[i + q] |= x as u32;
            r[i + q + 1] |= (x >> 32) as u32;
        }
        let mut out = Big { w: r };
        out.trim();
        out
    }

    pub fn shr(&self, n: usize) -> Self {
        if n == 0 {
            return self.clone();
        }
        if self.fits_u64() && n < 64 {
            return Big::from_u64(self.to_u64() >> n);
        }
        let q = n / 32;
        let s = n % 32;
        if q >= self.w.len() {
            return Big::zero();
        }
        let mut r = vec![0u32; self.w.len() - q];
        for i in q..self.w.len() {
            let mut x = self.w[i] as u64;
            if i + 1 < self.w.len() {
                x |= (self.w[i + 1] as u64) << 32;
            }
            r[i - q] = (x >> s) as u32;
        }
        let mut out = Big { w: r };
        out.trim();
        out
    }

    fn trim(&mut self) {
        while self.w.last() == Some(&0) {
            self.w.pop();
        }
    }

    pub fn isqrt(a: &Big) -> Big {
        if a.is_zero() {
            return a.clone();
        }
        let mut x = Big::two_to((a.bits() + 1) / 2);
        loop {
            let (q, _r) = Big::divmod(a, &x);
            let y = Big::add(&x, &q).shr(1);
            if Big::cmp(&y, &x) != Ordering::Less {
                return x;
            }
            x = y;
        }
    }

    pub fn pow(mut a: Big, mut n: u64) -> Big {
        let mut r = Big::from_u64(1);
        while n != 0 {
            if n & 1 != 0 {
                r = Big::mul(&r, &a);
            }
            n >>= 1;
            if n != 0 {
                a = Big::mul(&a, &a);
            }
        }
        r
    }

    pub fn add(a: &Big, b: &Big) -> Big {
        let n = a.w.len().max(b.w.len()) + 1;
        let mut r = vec![0u32; n];
        let mut c = 0u64;
        for i in 0..n {
            c += a.w.get(i).copied().unwrap_or(0) as u64;
            c += b.w.get(i).copied().unwrap_or(0) as u64;
            r[i] = c as u32;
            c >>= 32;
        }
        let mut out = Big { w: r };
        out.trim();
        out
    }

    /// a - b; requires a >= b.
    pub fn sub(a: &Big, b: &Big) -> Big {
        assert!(Big::cmp(a, b) != Ordering::Less, "Big: a difference would be negative");
        let mut r = vec![0u32; a.w.len()];
        let mut c: i64 = 0;
        for i in 0..a.w.len() {
            c += a.w[i] as i64 - b.w.get(i).copied().unwrap_or(0) as i64;
            r[i] = c as u32;
            c >>= 32;
        }
        let mut out = Big { w: r };
        out.trim();
        out
    }

    pub fn mul(a: &Big, b: &Big) -> Big {
        if a.is_zero() || b.is_zero() {
            return Big::zero();
        }
        // The common small case: both operands fit one limb.
        if a.w.len() == 1 && b.w.len() == 1 {
            return Big::from_u64((a.w[0] as u64) * (b.w[0] as u64));
        }
        let mut r = vec![0u32; a.w.len() + b.w.len()];
        for i in 0..a.w.len() {
            let mut c = 0u64;
            for j in 0..b.w.len() {
                c += (a.w[i] as u64) * (b.w[j] as u64) + r[i + j] as u64;
                r[i + j] = c as u32;
                c >>= 32;
            }
            r[i + b.w.len()] = c as u32;
        }
        let mut out = Big { w: r };
        out.trim();
        out
    }

    /// `q = floor(a / b)`, `r = a - q b` (`Big::divmod`, Knuth's Algorithm D).
    pub fn divmod(a: &Big, b: &Big) -> (Big, Big) {
        assert!(!b.is_zero(), "Big: division by zero");
        // The common case: both operands fit one 64-bit word. The limb loops (and the Knuth
        // normalisation) are then pure overhead.
        if a.fits_u64() && b.fits_u64() {
            let av = a.to_u64();
            let bv = b.to_u64();
            return (Big::from_u64(av / bv), Big::from_u64(av % bv));
        }
        if Big::cmp(a, b) == Ordering::Less {
            return (Big::zero(), a.clone());
        }
        if b.w.len() == 1 {
            let b0 = b.w[0] as u64;
            let mut t = vec![0u32; a.w.len()];
            let mut c = 0u64;
            for i in (0..a.w.len()).rev() {
                c = (c << 32) | a.w[i] as u64;
                t[i] = (c / b0) as u32;
                c %= b0;
            }
            let mut q = Big { w: t };
            q.trim();
            return (q, Big::from_u64(c));
        }
        let mut s = 0usize;
        let mut top = b.w[b.w.len() - 1];
        while top & 0x8000_0000 == 0 {
            top <<= 1;
            s += 1;
        }
        // With no normalisation shift the divisor can be read where it is; `shl(0)` would copy it.
        let v_owned;
        let v: &Big = if s == 0 {
            b
        } else {
            v_owned = b.shl(s);
            &v_owned
        };
        let mut u = a.shl(s);
        let n = v.w.len();
        let want = u.w.len().max(a.w.len() + 1);
        u.w.resize(want, 0);
        let m = u.w.len() - n - 1;
        let mut t = vec![0u32; m + 1];
        for j in (0..=m).rev() {
            let num = ((u.w[j + n] as u64) << 32) | u.w[j + n - 1] as u64;
            let mut qh = num / v.w[n - 1] as u64;
            let mut rh = num % v.w[n - 1] as u64;
            while qh >> 32 != 0
                || qh * (v.w[n - 2] as u64) > ((rh << 32) | u.w[j + n - 2] as u64)
            {
                qh -= 1;
                rh += v.w[n - 1] as u64;
                if rh >> 32 != 0 {
                    break;
                }
            }
            let mut borrow: i64 = 0;
            let mut carry: u64 = 0;
            for i in 0..n {
                carry += qh * v.w[i] as u64;
                let d = u.w[i + j] as i64 - (carry as u32) as i64 + borrow;
                u.w[i + j] = d as u32;
                borrow = d >> 32;
                carry >>= 32;
            }
            let d = u.w[j + n] as i64 - carry as i64 + borrow;
            u.w[j + n] = d as u32;
            if d < 0 {
                qh -= 1;
                let mut c = 0u64;
                for i in 0..n {
                    c += u.w[i + j] as u64 + v.w[i] as u64;
                    u.w[i + j] = c as u32;
                    c >>= 32;
                }
                u.w[j + n] = u.w[j + n].wrapping_add(c as u32);
            }
            t[j] = qh as u32;
        }
        let mut q = Big { w: t };
        q.trim();
        let mut r = u;
        r.trim();
        (q, r.shr(s))
    }
}

impl Add for Big {
    type Output = Big;
    fn add(self, o: Big) -> Big {
        Big::add(&self, &o)
    }
}
impl Sub for Big {
    type Output = Big;
    fn sub(self, o: Big) -> Big {
        Big::sub(&self, &o)
    }
}
impl Mul for Big {
    type Output = Big;
    fn mul(self, o: Big) -> Big {
        Big::mul(&self, &o)
    }
}
impl Mul for &Big {
    type Output = Big;
    fn mul(self, o: &Big) -> Big {
        Big::mul(self, o)
    }
}
impl PartialOrd for Big {
    fn partial_cmp(&self, o: &Big) -> Option<Ordering> {
        Some(Big::cmp(self, o))
    }
}

/// A rounding direction (`Dir`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    Down,
    Up,
}

/// `m * 2^e` (`Real`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Real {
    pub m: Big,
    pub e: i64,
}

impl Real {
    pub fn from_u64(x: u64) -> Self {
        Real { m: Big::from_u64(x), e: 0 }
    }
    pub fn from_big(x: Big) -> Self {
        Real { m: x, e: 0 }
    }
    pub fn from_big_exp(x: Big, e: i64) -> Self {
        Real { m: x, e }
    }
    pub fn two_to(n: i64) -> Self {
        Real { m: Big::from_u64(1), e: n }
    }
    pub fn zero(&self) -> bool {
        self.m.is_zero()
    }
    /// `2^(top-1) <= value < 2^top`.
    pub fn top(&self) -> i64 {
        self.m.bits() as i64 + self.e
    }

    pub fn cut(&self, d: Dir) -> Real {
        let b = self.m.bits();
        if b <= REAL_BITS {
            return self.clone();
        }
        let s = b - REAL_BITS;
        let mut r = Real { m: self.m.shr(s), e: self.e + s as i64 };
        if d == Dir::Up && self.m.any_below(s) {
            r.m = Big::add(&r.m, &Big::from_u64(1));
        }
        r
    }

    pub fn cmp(a: &Real, b: &Real) -> Ordering {
        if a.zero() || b.zero() {
            return if a.zero() {
                if b.zero() { Ordering::Equal } else { Ordering::Less }
            } else {
                Ordering::Greater
            };
        }
        if a.top() != b.top() {
            return a.top().cmp(&b.top());
        }
        if a.e >= b.e {
            Big::cmp(&a.m.shl((a.e - b.e) as usize), &b.m)
        } else {
            Big::cmp(&a.m, &b.m.shl((b.e - a.e) as usize))
        }
    }

    pub fn add(a: &Real, b: &Real, d: Dir) -> Real {
        if a.zero() {
            return b.clone();
        }
        if b.zero() {
            return a.clone();
        }
        let e = a.e.min(b.e);
        Real {
            m: Big::add(
                &a.m.shl((a.e - e) as usize),
                &b.m.shl((b.e - e) as usize),
            ),
            e,
        }
        .cut(d)
    }

    /// a - b for a >= b.
    pub fn sub(a: &Real, b: &Real, d: Dir) -> Real {
        if b.zero() {
            return a.clone();
        }
        let e = a.e.min(b.e);
        Real {
            m: Big::sub(
                &a.m.shl((a.e - e) as usize),
                &b.m.shl((b.e - e) as usize),
            ),
            e,
        }
        .cut(d)
    }

    pub fn mul(a: &Real, b: &Real, d: Dir) -> Real {
        Real { m: Big::mul(&a.m, &b.m), e: a.e + b.e }.cut(d)
    }

    pub fn div(a: &Real, b: &Real, d: Dir) -> Real {
        assert!(!b.zero(), "Real: division by zero");
        if a.zero() {
            return a.clone();
        }
        let s = REAL_BITS + 2 + b.m.bits();
        let (mut q, r) = Big::divmod(&a.m.shl(s), &b.m);
        if d == Dir::Up && !r.is_zero() {
            q = Big::add(&q, &Big::from_u64(1));
        }
        Real { m: q, e: a.e - s as i64 - b.e }.cut(d)
    }

    pub fn sqrt(a: &Real, d: Dir) -> Real {
        if a.zero() {
            return a.clone();
        }
        let top = a.top();
        let mut root_top = top / 2;
        if 2 * root_top < top {
            root_top += 1;
        }
        let unit = root_top - REAL_BITS as i64;
        let shift = a.e - 2 * unit;
        let whole = if shift >= 0 {
            a.m.shl(shift as usize)
        } else {
            a.m.shr((-shift) as usize)
        };
        let fraction = shift < 0 && a.m.any_below((-shift) as usize);
        let mut root = Big::isqrt(&whole);
        if d == Dir::Up && (fraction || Big::cmp(&Big::mul(&root, &root), &whole) != Ordering::Equal) {
            root = Big::add(&root, &Big::from_u64(1));
        }
        Real { m: root, e: unit }
    }

    pub fn pow(mut a: Real, mut n: u64, d: Dir) -> Real {
        let mut r = Real::from_u64(1);
        while n != 0 {
            if n & 1 != 0 {
                r = Real::mul(&r, &a, d);
            }
            if n > 1 {
                a = Real::mul(&a, &a, d);
            }
            n >>= 1;
        }
        r
    }

    pub fn floor(&self) -> Big {
        if self.e >= 0 {
            self.m.shl(self.e as usize)
        } else {
            self.m.shr((-self.e) as usize)
        }
    }

    pub fn ceil(&self) -> Big {
        if self.e >= 0 {
            self.m.shl(self.e as usize)
        } else {
            let r = self.m.shr((-self.e) as usize);
            if self.m.any_below((-self.e) as usize) {
                Big::add(&r, &Big::from_u64(1))
            } else {
                r
            }
        }
    }

    /// For printed figures only.
    pub fn log2(&self) -> f64 {
        if self.zero() {
            return f64::NEG_INFINITY;
        }
        let b = self.m.bits();
        let t = if b > 64 { self.m.shr(b - 64) } else { self.m.shl(64 - b) };
        self.top() as f64 + libm::log2(t.to_u64() as f64 / 18_446_744_073_709_551_616.0)
    }

    pub fn value(&self) -> f64 {
        if self.zero() {
            0.0
        } else {
            libm::exp2(self.log2())
        }
    }
}

impl PartialOrd for Real {
    fn partial_cmp(&self, o: &Real) -> Option<Ordering> {
        Some(Real::cmp(self, o))
    }
}

/// `lo <= true value <= hi` (`Bound`).
#[derive(Clone, Debug, Default)]
pub struct Bound {
    pub lo: Real,
    pub hi: Real,
    pub bad: bool,
}

impl Bound {
    pub fn from_u64(x: u64) -> Self {
        Bound { lo: Real::from_u64(x), hi: Real::from_u64(x), bad: false }
    }
    pub fn from_big(x: &Big) -> Self {
        Bound {
            lo: Real::from_big(x.clone()).cut(Dir::Down),
            hi: Real::from_big(x.clone()).cut(Dir::Up),
            bad: false,
        }
    }
    pub fn from_real(x: &Real) -> Self {
        Bound { lo: x.clone(), hi: x.clone(), bad: false }
    }
    pub fn from_pair(l: Real, h: Real) -> Self {
        let bad = Real::cmp(&h, &l) == Ordering::Less;
        Bound { lo: l, hi: h, bad }
    }
    pub fn ratio(a: &Big, b: &Big) -> Self {
        Bound::from_big(a) / Bound::from_big(b)
    }
    pub fn failed() -> Self {
        Bound { lo: Real::from_u64(1), hi: Real::from_u64(1), bad: true }
    }
    pub fn inherit(mut self, a: &Bound, b: &Bound) -> Self {
        self.bad = self.bad || a.bad || b.bad;
        self
    }
    pub fn error(&self) -> Real {
        if self.bad {
            Real::from_u64(1)
        } else {
            self.hi.clone()
        }
    }
    pub fn sqrt(a: &Bound) -> Self {
        Bound::from_pair(Real::sqrt(&a.lo, Dir::Down), Real::sqrt(&a.hi, Dir::Up)).inherit(a, a)
    }
    pub fn pow(a: &Bound, n: u64) -> Self {
        Bound::from_pair(Real::pow(a.lo.clone(), n, Dir::Down), Real::pow(a.hi.clone(), n, Dir::Up))
            .inherit(a, a)
    }
}

impl Add for Bound {
    type Output = Bound;
    fn add(self, o: Bound) -> Bound {
        Bound::from_pair(
            Real::add(&self.lo, &o.lo, Dir::Down),
            Real::add(&self.hi, &o.hi, Dir::Up),
        )
        .inherit(&self, &o)
    }
}
impl Sub for Bound {
    type Output = Bound;
    fn sub(self, o: Bound) -> Bound {
        if self.bad || o.bad || !(o.hi < self.lo) {
            return Bound::failed();
        }
        Bound::from_pair(
            Real::sub(&self.lo, &o.hi, Dir::Down),
            Real::sub(&self.hi, &o.lo, Dir::Up),
        )
    }
}
impl Mul for Bound {
    type Output = Bound;
    fn mul(self, o: Bound) -> Bound {
        Bound::from_pair(
            Real::mul(&self.lo, &o.lo, Dir::Down),
            Real::mul(&self.hi, &o.hi, Dir::Up),
        )
        .inherit(&self, &o)
    }
}
impl core::ops::Div for Bound {
    type Output = Bound;
    fn div(self, o: Bound) -> Bound {
        if self.bad || o.bad || o.lo.zero() {
            return Bound::failed();
        }
        Bound::from_pair(
            Real::div(&self.lo, &o.hi, Dir::Down),
            Real::div(&self.hi, &o.lo, Dir::Up),
        )
    }
}

impl From<u64> for Bound {
    fn from(x: u64) -> Bound {
        Bound::from_u64(x)
    }
}
impl From<&Big> for Bound {
    fn from(x: &Big) -> Bound {
        Bound::from_big(x)
    }
}
impl From<&Real> for Bound {
    fn from(x: &Real) -> Bound {
        Bound::from_real(x)
    }
}

/// Certainly `a <= b` (`surely_le`).
pub fn surely_le(a: &Bound, b: &Bound) -> bool {
    !a.bad && !b.bad && a.hi <= b.lo
}
/// Certainly `a < b` (`surely_lt`).
pub fn surely_lt(a: &Bound, b: &Bound) -> bool {
    !a.bad && !b.bad && a.hi < b.lo
}

/// Minus log2 of an error (`bits_of`).
pub fn bits_of(error: &Real) -> f64 {
    if error.zero() {
        f64::INFINITY
    } else {
        -error.log2()
    }
}

/// `cut2`: round down to two decimals (`real.h`).
pub fn cut2(x: f64) -> f64 {
    if x.is_finite() {
        libm::floor(100.0 * x) / 100.0
    } else {
        x
    }
}

/// A decimal string for logs; not used by decisions.
pub fn real_debug(r: &Real) -> String {
    alloc::format!("{}*2^{}", r.m.w.len(), r.e)
}
