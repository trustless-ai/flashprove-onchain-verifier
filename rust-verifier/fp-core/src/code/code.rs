//! The linear codes of `blocks/code/code.h`: plain Reed-Solomon on Goldilocks cosets, with the
//! randomized encoding `symbol = message_scale * sum message[j] f^j + tail_scale * sum tail[j] f^j`.

use alloc::vec;
use alloc::vec::Vec;

use super::cosets::{
    gl64_factors, gl64_subgroup_log, gl64_table, GL64_MOST_LOG_N,
};
use super::short_position::short_position;
use crate::field::ext::{F, E};
use crate::field::mle::{product_index, product_table};

/// The largest `log_n` that `code_ok()` accepts.
pub const CODE_MOST_LOG_N: u32 = GL64_MOST_LOG_N;

/// A code's three numbers (`Code`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Code {
    pub log_n: u32,
    pub ell: usize,
    pub r: usize,
}

impl Code {
    pub fn n(&self) -> u64 {
        1u64 << self.log_n
    }
    pub fn message_at(&self) -> u64 {
        self.r as u64
    }
    pub fn tail_at(&self) -> u64 {
        0
    }
    pub fn dim(&self) -> u64 {
        self.ell as u64 + self.r as u64
    }
    pub fn log_dim(&self) -> u32 {
        crate::numbers::codes::ceil_log2(self.dim())
    }
    pub fn log_ell(&self) -> u32 {
        crate::numbers::codes::ceil_log2(self.ell as u64)
    }
    pub fn log_r(&self) -> u32 {
        crate::numbers::codes::ceil_log2(self.r as u64)
    }
    pub fn rate(&self) -> f64 {
        self.dim() as f64 / self.n() as f64
    }
}

/// Whether the numbers describe a code (`code_ok`).
pub fn code_ok(c: &Code) -> bool {
    if c.log_n < 1 || c.log_n > CODE_MOST_LOG_N || c.ell < 1 {
        return false;
    }
    if c.ell as u64 > c.n() || c.r as u64 > c.n() || c.dim() > c.n() {
        return false;
    }
    if c.dim() > (1u64 << gl64_subgroup_log(c.log_n)) {
        return false;
    }
    true
}

pub fn min_distance(c: &Code) -> u64 {
    c.n() - c.dim() + 1
}

pub fn hiding_positions(c: &Code) -> u64 {
    c.r as u64
}

pub fn tail_for_positions(t: u64) -> u64 {
    t
}

pub fn mask_fits(main: &Code, mask: &Code) -> bool {
    mask.log_n <= main.log_n
}

pub fn mask_position(main: &Code, mask: &Code, x: u64) -> u64 {
    short_position(main.log_n, mask.log_n, x)
}

/// `f[0..count)` at position `x` (`factors`); a count above 64 is cut to 64.
pub fn factors(c: &Code, x: u64, count: u32, f: &mut [F]) {
    let count = count.min(64) as usize;
    let mut w = [0u64; 64];
    gl64_factors(c.log_n, x, count, &mut w);
    for i in 0..count {
        f[i] = F(w[i]);
    }
}

pub fn basis_at(f: &[F], count: u32, j: u64) -> F {
    product_index(f, count as usize, j)
}

pub fn message_scale(c: &Code, f: &[F]) -> F {
    basis_at(f, c.log_dim(), c.message_at())
}

pub fn tail_scale(c: &Code, f: &[F]) -> F {
    basis_at(f, c.log_dim(), c.tail_at())
}

/// What the formula needs at one position (`GeneratorRow`).
#[derive(Clone, Copy, Debug)]
pub struct GeneratorRow {
    pub message_scale: F,
    pub tail_scale: F,
    pub f: [F; 64],
}

pub fn generator_at(c: &Code, x: u64) -> GeneratorRow {
    let mut g = GeneratorRow { message_scale: F::zero(), tail_scale: F::zero(), f: [F::zero(); 64] };
    factors(c, x, c.log_dim(), &mut g.f);
    g.message_scale = message_scale(c, &g.f);
    g.tail_scale = tail_scale(c, &g.f);
    g
}

/// Row `x` of the generator matrix (`generator_row`).
pub fn generator_row(c: &Code, x: u64, on_message: Option<&mut [F]>, on_tail: Option<&mut [F]>) {
    let g = generator_at(c, x);
    if let Some(m) = on_message {
        product_table(&g.f, c.log_ell() as usize, c.ell, m);
        for v in m.iter_mut().take(c.ell) {
            *v = *v * g.message_scale;
        }
    }
    if let Some(t) = on_tail {
        product_table(&g.f, c.log_r() as usize, c.r, t);
        for v in t.iter_mut().take(c.r) {
            *v = *v * g.tail_scale;
        }
    }
}

/// The element type that `Encoder` writes.
pub trait FieldLike: Copy + PartialEq {
    fn zero() -> Self;
    fn add(self, o: Self) -> Self;
    fn sub(self, o: Self) -> Self;
    fn mul_f(self, f: F) -> Self;
}

impl FieldLike for F {
    fn zero() -> Self {
        F::zero()
    }
    fn add(self, o: Self) -> Self {
        self + o
    }
    fn sub(self, o: Self) -> Self {
        self - o
    }
    fn mul_f(self, f: F) -> Self {
        self * f
    }
}

impl FieldLike for E {
    fn zero() -> Self {
        E::zero()
    }
    fn add(self, o: Self) -> Self {
        self + o
    }
    fn sub(self, o: Self) -> Self {
        self - o
    }
    fn mul_f(self, f: F) -> Self {
        self * f
    }
}

fn product_dot_typed<T: FieldLike>(v: &[T], len: usize, f: &[F], k: usize) -> T {
    assert!(k < 64 && len <= (1usize << k), "product_dot: vector longer than the form");
    if len == 0 {
        return T::zero();
    }
    let mut a: Vec<T> = v[..len].to_vec();
    let mut m = len;
    let mut t = 0;
    while t < k && m > 1 {
        let h = (m + 1) / 2;
        for j in 0..h {
            a[j] = if 2 * j + 1 < m {
                a[2 * j].add(a[2 * j + 1].mul_f(f[t]))
            } else {
                a[2 * j]
            };
        }
        m = h;
        t += 1;
    }
    a[0]
}

/// The symbol at `x` of a row over F or E (`symbol_at`).
pub fn symbol_at<T: FieldLike>(c: &Code, x: u64, message: &[T], tail: &[T]) -> T {
    let g = generator_at(c, x);
    product_dot_typed(message, c.ell, &g.f, c.log_ell() as usize)
        .mul_f(g.message_scale)
        .add(product_dot_typed(tail, c.r, &g.f, c.log_r() as usize).mul_f(g.tail_scale))
}

/// Encodes rows of one code (`Encoder`). The transform table is built in the constructor; the C++
/// version caches it under a mutex, which a single-threaded `no_std` core does not need.
#[derive(Clone, Debug)]
pub struct Encoder {
    code: Code,
    tw: Vec<F>,
}

impl Encoder {
    pub fn new(c: Code) -> Self {
        assert!(code_ok(&c), "encoder: these numbers are not a code");
        let tw = gl64_table(c.log_n, gl64_subgroup_log(c.log_n)).into_iter().map(F).collect();
        Encoder { code: c, tw }
    }

    pub fn code(&self) -> &Code {
        &self.code
    }

    pub fn encode<T: FieldLike>(&self, message: &[T], tail: &[T], word: &mut [T]) {
        let block = 1usize << self.code.log_dim();
        for w in word[..block].iter_mut() {
            *w = T::zero();
        }
        for j in 0..self.code.ell {
            word[self.code.message_at() as usize + j] = message[j];
        }
        for j in 0..self.code.r {
            word[self.code.tail_at() as usize + j] = tail[j];
        }
        self.evaluate(word);
    }

    /// In place: coefficients to evaluations (`evaluate`).
    pub fn evaluate<T: FieldLike>(&self, word: &mut [T]) {
        let n = self.code.n() as usize;
        let ld = self.code.log_dim();
        let mut at = 1usize << ld;
        while at < n {
            for j in 0..at {
                word[at + j] = word[j];
            }
            at <<= 1;
        }
        let mut l = ld;
        while l > 0 {
            l -= 1;
            let st = 1usize << l;
            let t = &self.tw[(n >> (l + 1))..];
            for h in 0..(n >> (l + 1)) {
                let a0 = 2 * st * h;
                let (a, b) = word[a0..a0 + 2 * st].split_at_mut(st);
                for j in 0..st {
                    let u = a[j];
                    let v = b[j].mul_f(t[h]);
                    a[j] = u.add(v);
                    b[j] = u.sub(v);
                }
            }
        }
    }

    /// The inverse of `encode()`, for tests (`decode`).
    pub fn decode<T: FieldLike>(&self, word: &[T], message: &mut [T], tail: &mut [T]) -> bool {
        let n = self.code.n() as usize;
        let top = gl64_subgroup_log(self.code.log_n) as usize;
        let block = 1usize << top;
        let mut a: Vec<T> = word[..block].to_vec();
        let half = (F::one() + F::one()).inv();
        for l in 0..top {
            let st = 1usize << l;
            let t = &self.tw[(n >> (l + 1))..];
            for h in 0..(block >> (l + 1)) {
                let back = half * t[h].inv();
                let a0 = 2 * st * h;
                let (p, q) = a[a0..a0 + 2 * st].split_at_mut(st);
                for j in 0..st {
                    let u = p[j];
                    let v = q[j];
                    p[j] = u.add(v).mul_f(half);
                    q[j] = u.sub(v).mul_f(back);
                }
            }
        }
        for j in 0..self.code.ell {
            message[j] = a[self.code.message_at() as usize + j];
        }
        for j in 0..self.code.r {
            tail[j] = a[self.code.tail_at() as usize + j];
        }
        let mut again = vec![T::zero(); n];
        self.encode(message, tail, &mut again);
        for i in 0..n {
            if again[i] != word[i] {
                return false;
            }
        }
        true
    }
}

/// Encodes one row (`encode` convenience).
pub fn encode_f(c: &Code, message: &[F], tail: &[F], word: &mut [F]) {
    Encoder::new(*c).encode(message, tail, word);
}
pub fn encode_e(c: &Code, message: &[E], tail: &[E], word: &mut [E]) {
    Encoder::new(*c).encode(message, tail, word);
}
