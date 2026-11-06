//! The base field F = Z/p and its cubic extension E = F[X]/(X^3 - 2), ported from
//! `blocks/field/field.h`.
//!
//! An F stores the canonical word below p. An E stores the coordinates of 1, X and X^2 in order.
//! In bytes, F is 8 little-endian bytes and E is 24. As in C++, arguments are assumed canonical
//! and results are canonical.

use super::gl64;

/// The base field element.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct F(pub u64);

/// The cubic extension element: `c[0] + c[1] X + c[2] X^2`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct E(pub [F; 3]);

impl F {
    #[inline]
    pub const fn zero() -> Self {
        F(0)
    }
    #[inline]
    pub const fn one() -> Self {
        F(1)
    }
    /// The residue of `v` modulo p (`from_u64`).
    #[inline]
    pub const fn from_u64(v: u64) -> Self {
        F(gl64::from_u64(v))
    }
    /// The residue of `v` modulo p, negative or not (`from_i64`).
    #[inline]
    pub const fn from_i64(v: i64) -> Self {
        if v < 0 {
            F(gl64::neg(gl64::from_u64((v as u64).wrapping_neg())))
        } else {
            F(gl64::from_u64(v as u64))
        }
    }
    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }
    /// x^e, with x^0 = 1 also for x = 0 (`pow(F, u64)`).
    #[inline]
    pub fn pow(self, mut e: u64) -> Self {
        let mut r = F::one();
        let mut x = self;
        while e != 0 {
            if e & 1 != 0 {
                r = r * x;
            }
            e >>= 1;
            x = x * x;
        }
        r
    }
    /// 1/x, and 0 for x = 0 (`inv(F)`).
    #[inline]
    pub fn inv(self) -> Self {
        self.pow(gl64::P - 2)
    }
    /// `F_from_word`: one rejection-sampling step.
    #[inline]
    pub const fn from_word(w: u64) -> Option<Self> {
        match gl64::from_word(w) {
            Some(v) => Some(F(v)),
            None => None,
        }
    }
    /// `F_from_bytes`: little-endian, false (and zero) unless the word is below p.
    #[inline]
    pub fn from_bytes(b: &[u8; 8]) -> Option<Self> {
        let w = u64::from_le_bytes(*b);
        if w < gl64::P {
            Some(F(w))
        } else {
            None
        }
    }
    #[inline]
    pub const fn to_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }
}

impl E {
    #[inline]
    pub const fn zero() -> Self {
        E([F::zero(); 3])
    }
    #[inline]
    pub const fn one() -> Self {
        E([F::one(), F::zero(), F::zero()])
    }
    /// The embedding of a base-field element (`E::from(F)`).
    #[inline]
    pub const fn from_base(a: F) -> Self {
        E([a, F::zero(), F::zero()])
    }
    #[inline]
    pub const fn from_parts(a: F, b: F, c: F) -> Self {
        E([a, b, c])
    }
    /// X^i for i = 0, 1, 2; zero for a larger i (`E::theta`).
    #[inline]
    pub const fn theta(i: usize) -> Self {
        E([
            F(if i == 0 { 1 } else { 0 }),
            F(if i == 1 { 1 } else { 0 }),
            F(if i == 2 { 1 } else { 0 }),
        ])
    }
    #[inline]
    pub const fn is_zero(self) -> bool {
        (self.0[0].0 | self.0[1].0 | self.0[2].0) == 0
    }
    /// `inv(E)`: 0 for x = 0.
    #[inline]
    pub fn inv(self) -> Self {
        let a = self.0[0];
        let b = self.0[1];
        let c = self.0[2];
        let nr = F::from_u64(gl64::NR);
        let big_a = a * a - nr * (b * c);
        let big_b = nr * (c * c) - a * b;
        let big_c = b * b - a * c;
        let n = (a * big_a + nr * (b * big_c + c * big_b)).inv();
        E([big_a * n, big_b * n, big_c * n])
    }
    /// x^e, with x^0 = 1 also for x = 0 (`pow(E, u64)`).
    #[inline]
    pub fn pow(self, mut e: u64) -> Self {
        let mut r = E::one();
        let mut x = self;
        while e != 0 {
            if e & 1 != 0 {
                r = r * x;
            }
            e >>= 1;
            x = x * x;
        }
        r
    }
    /// `E_from_bytes`: 24 little-endian bytes; false and zero if any coordinate is not below p.
    #[inline]
    pub fn from_bytes(b: &[u8; 24]) -> Option<Self> {
        let mut c = [F::zero(); 3];
        let mut ok = true;
        for i in 0..3 {
            match F::from_bytes(b[8 * i..8 * i + 8].try_into().unwrap()) {
                Some(f) => c[i] = f,
                None => ok = false,
            }
        }
        if ok {
            Some(E(c))
        } else {
            None
        }
    }
    #[inline]
    pub const fn to_bytes(self) -> [u8; 24] {
        let mut b = [0u8; 24];
        let a0 = self.0[0].to_bytes();
        let a1 = self.0[1].to_bytes();
        let a2 = self.0[2].to_bytes();
        let mut i = 0;
        while i < 8 {
            b[i] = a0[i];
            b[8 + i] = a1[i];
            b[16 + i] = a2[i];
            i += 1;
        }
        b
    }
}

impl core::ops::Add for F {
    type Output = F;
    #[inline]
    fn add(self, o: F) -> F {
        F(gl64::add(self.0, o.0))
    }
}
impl core::ops::Sub for F {
    type Output = F;
    #[inline]
    fn sub(self, o: F) -> F {
        F(gl64::sub(self.0, o.0))
    }
}
impl core::ops::Neg for F {
    type Output = F;
    #[inline]
    fn neg(self) -> F {
        F(gl64::neg(self.0))
    }
}
impl core::ops::Mul for F {
    type Output = F;
    #[inline]
    fn mul(self, o: F) -> F {
        F(gl64::mul(self.0, o.0))
    }
}
impl core::ops::AddAssign for F {
    #[inline]
    fn add_assign(&mut self, o: F) {
        *self = *self + o;
    }
}
impl core::ops::SubAssign for F {
    #[inline]
    fn sub_assign(&mut self, o: F) {
        *self = *self - o;
    }
}
impl core::ops::MulAssign for F {
    #[inline]
    fn mul_assign(&mut self, o: F) {
        *self = *self * o;
    }
}

impl core::ops::Add for E {
    type Output = E;
    #[inline]
    fn add(self, o: E) -> E {
        E([self.0[0] + o.0[0], self.0[1] + o.0[1], self.0[2] + o.0[2]])
    }
}
impl core::ops::Sub for E {
    type Output = E;
    #[inline]
    fn sub(self, o: E) -> E {
        E([self.0[0] - o.0[0], self.0[1] - o.0[1], self.0[2] - o.0[2]])
    }
}
impl core::ops::Neg for E {
    type Output = E;
    #[inline]
    fn neg(self) -> E {
        E([-self.0[0], -self.0[1], -self.0[2]])
    }
}
/// The lazy-reduction product of `field.h`, with the same three `dot3` calls.
impl core::ops::Mul for E {
    type Output = E;
    #[inline]
    fn mul(self, o: E) -> E {
        let a0 = self.0[0].0;
        let a1 = self.0[1].0;
        let a2 = self.0[2].0;
        let b0 = o.0[0].0;
        let b1 = o.0[1].0;
        let b2 = o.0[2].0;
        let n1 = gl64::times_nr(b1);
        let n2 = gl64::times_nr(b2);
        E([
            F(gl64::dot3(a0, b0, a1, n2, a2, n1)),
            F(gl64::dot3(a0, b1, a1, b0, a2, n2)),
            F(gl64::dot3(a0, b2, a1, b1, a2, b0)),
        ])
    }
}
impl core::ops::Mul<F> for E {
    type Output = E;
    #[inline]
    fn mul(self, b: F) -> E {
        E([self.0[0] * b, self.0[1] * b, self.0[2] * b])
    }
}
impl core::ops::Mul<E> for F {
    type Output = E;
    #[inline]
    fn mul(self, a: E) -> E {
        a * self
    }
}
impl core::ops::Add<F> for E {
    type Output = E;
    #[inline]
    fn add(self, b: F) -> E {
        E([self.0[0] + b, self.0[1], self.0[2]])
    }
}
impl core::ops::Sub<F> for E {
    type Output = E;
    #[inline]
    fn sub(self, b: F) -> E {
        E([self.0[0] - b, self.0[1], self.0[2]])
    }
}
impl core::ops::AddAssign for E {
    #[inline]
    fn add_assign(&mut self, o: E) {
        *self = *self + o;
    }
}
impl core::ops::SubAssign for E {
    #[inline]
    fn sub_assign(&mut self, o: E) {
        *self = *self - o;
    }
}
impl core::ops::MulAssign for E {
    #[inline]
    fn mul_assign(&mut self, o: E) {
        *self = *self * o;
    }
}
impl core::ops::MulAssign<F> for E {
    #[inline]
    fn mul_assign(&mut self, o: F) {
        *self = *self * o;
    }
}
