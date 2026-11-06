//! HP: the hiding polynomial of a sumcheck and `Weight`, how one variable is summed. Ported from
//! `blocks/iop/hp.h` (lines 32-275). Arithmetic only; messages and masks stay with the callers.
//!
//! The round polynomials depend on the witness, so PSC and FOLD run their sumcheck on `U + eps*G`:
//! `U` (the hiding polynomial below) has random coefficients, and its sum and round polynomials
//! are uniform among the tuples that pass the verifier's checks (hp.h's fact 2).

use alloc::vec;
use alloc::vec::Vec;

/// The field operations that `hp.h` asks of its template parameter `K` (hp.h:20-22): default
/// construction, `+ - *`, `==`, `K::zero()`, `K::one()` and `inv`.
pub trait ChallengeField:
    Copy
    + Clone
    + PartialEq
    + core::fmt::Debug
    + core::ops::Add<Output = Self>
    + core::ops::Sub<Output = Self>
    + core::ops::Mul<Output = Self>
    + core::ops::Neg<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
    fn inv(self) -> Self;
}

impl ChallengeField for crate::field::ext::F {
    fn zero() -> Self {
        crate::field::ext::F::zero()
    }
    fn one() -> Self {
        crate::field::ext::F::one()
    }
    fn inv(self) -> Self {
        crate::field::ext::F::inv(self)
    }
}

impl ChallengeField for crate::field::ext::E {
    fn zero() -> Self {
        crate::field::ext::E::zero()
    }
    fn one() -> Self {
        crate::field::ext::E::one()
    }
    fn inv(self) -> Self {
        crate::field::ext::E::inv(self)
    }
}

/// `poly_at(g, x)`: the coefficients of `g`, lowest degree first, at `x` (hp.h:34-39).
pub fn poly_at<K: ChallengeField>(g: &[K], x: K) -> K {
    let mut r = K::zero();
    for t in (0..g.len()).rev() {
        r = r * x + g[t];
    }
    r
}

/// The integer `n` as an element of `K`, by n additions (`small_int`, hp.h:42-47).
pub fn small_int<K: ChallengeField>(n: u32) -> K {
    let mut r = K::zero();
    for _ in 0..n {
        r = r + K::one();
    }
    r
}

/// The polynomial of degree below `values.len()` that takes `values[i]` at the node `i`, by
/// Newton's divided differences (`poly_from_values_at_0_1_2`, hp.h:49-66). The nodes must be
/// distinct in K.
pub fn poly_from_values_at_0_1_2<K: ChallengeField>(mut values: Vec<K>) -> Vec<K> {
    let n = values.len();
    for s in 1..n {
        // values[i] becomes the divided difference on the nodes i-s .. i.
        let step = small_int::<K>(s as u32).inv();
        let mut i = n;
        while i > s {
            i -= 1;
            values[i] = (values[i] - values[i - 1]) * step;
        }
    }
    let mut g = vec![K::zero(); n];
    let mut i = n;
    while i > 0 {
        i -= 1;
        let node = small_int::<K>(i as u32);
        let mut t = n;
        while t > 1 {
            t -= 1;
            g[t] = g[t - 1] - node * g[t];
        }
        g[0] = values[i] - node * g[0];
    }
    g
}

/// How one variable is summed: a linear functional `phi` on polynomials with `d` coefficients,
/// and a polynomial `psi` with `phi(psi) = 1` (`Weight`, hp.h:70-162).
#[derive(Clone, Debug)]
pub struct Weight<K> {
    pub d: u32,
    pub moment: Vec<K>,
    pub psi: Vec<K>,
    pub fixed: u32,
    pub fixed_inv: K,
}

impl<K: ChallengeField> Weight<K> {
    /// `phi(g)` (`Weight::apply`, hp.h:85-90).
    pub fn apply(&self, g: &[K]) -> K {
        assert!(g.len() <= self.d as usize, "Weight::apply: the polynomial has too many coefficients");
        let mut r = K::zero();
        for t in 0..g.len() {
            r = r + self.moment[t] * g[t];
        }
        r
    }

    /// `phi(1)` (`Weight::of_one`, hp.h:91).
    pub fn of_one(&self) -> K {
        self.moment[0]
    }

    /// Sets `g[fixed]` so that `phi(g) = claim` (`Weight::complete`, hp.h:94-100).
    pub fn complete(&self, g: &mut [K], claim: K) {
        assert_eq!(g.len(), self.d as usize, "Weight::complete: the polynomial must have d coefficients");
        let mut rest = K::zero();
        for t in 0..self.d as usize {
            if t != self.fixed as usize {
                rest = rest + self.moment[t] * g[t];
            }
        }
        g[self.fixed as usize] = (claim - rest) * self.fixed_inv;
    }

    /// `phi(g) = g(0) + g(1)`; `psi = X` (`Weight::plain`, hp.h:102-109).
    pub fn plain(d: u32) -> Self {
        let mut w = Self::shell(d, 1);
        w.moment[0] = K::one() + K::one();
        for t in 1..d as usize {
            w.moment[t] = K::one();
        }
        w.psi = vec![K::zero(), K::one()];
        w.checked()
    }

    /// `phi(g) = (1-z) g(0) + z g(1)`; `psi = 1` (`Weight::equality`, hp.h:110-118).
    pub fn equality(z: K, d: u32) -> Self {
        let mut w = Self::shell(d, 0);
        w.moment[0] = K::one();
        for t in 1..d as usize {
            w.moment[t] = z;
        }
        w.psi = vec![K::one()];
        w.checked()
    }

    /// `phi(g) = g(0)` (`Weight::at_zero`, hp.h:119-120).
    pub fn at_zero(d: u32) -> Self {
        Self::equality(K::zero(), d)
    }

    /// `phi(g)` is the sum of g over the points, `psi = 1/|D|` (`Weight::domain`, hp.h:121-124).
    pub fn domain(points: &[K], d: u32) -> Self {
        Self::combination(points, &vec![K::one(); points.len()], d)
    }

    /// `phi(g) = sum_x Lag_x(z) g(x)` over the points, by the Lagrange polynomials of D
    /// (`Weight::lagrange`, hp.h:125-134). The points must be distinct.
    pub fn lagrange(points: &[K], z: K, d: u32) -> Self {
        let mut c = vec![K::one(); points.len()];
        for i in 0..points.len() {
            for j in 0..points.len() {
                if j != i {
                    c[i] = c[i] * (z - points[j]) * (points[i] - points[j]).inv();
                }
            }
        }
        Self::combination(points, &c, d)
    }

    fn shell(d: u32, fixed: u32) -> Self {
        assert!(d >= 2, "Weight: at least two coefficients");
        Weight {
            d,
            moment: vec![K::zero(); d as usize],
            psi: Vec::new(),
            fixed,
            fixed_inv: K::zero(),
        }
    }

    /// `phi(g) = sum_i c[i] g(points[i])`, `psi` the constant `1 / sum_i c[i]`
    /// (`Weight::combination`, hp.h:145-155).
    fn combination(points: &[K], c: &[K], d: u32) -> Self {
        let mut w = Self::shell(d, 0);
        for i in 0..points.len() {
            let mut power = c[i];
            for t in 0..d as usize {
                w.moment[t] = w.moment[t] + power;
                power = power * points[i];
            }
        }
        assert!(!(w.moment[0] == K::zero()), "Weight: the weights of the points sum to zero");
        w.psi = vec![w.moment[0].inv()];
        w.checked()
    }

    /// `Weight::checked`, hp.h:156-161.
    fn checked(mut self) -> Self {
        assert!(
            !(self.moment[self.fixed as usize] == K::zero()),
            "Weight: the check does not fix this coefficient"
        );
        self.fixed_inv = self.moment[self.fixed as usize].inv();
        assert!(
            self.psi.len() <= self.d as usize && self.apply(&self.psi) == K::one(),
            "Weight: phi(psi) must be 1"
        );
        self
    }
}

/// Number of random coefficients of U: `1 + sum_j (d_j - 1)` (`hp_entries`, hp.h:186-195).
pub fn hp_entries<K: ChallengeField>(vars: &[Weight<K>]) -> usize {
    let mut n = 1usize;
    for v in vars {
        assert!(v.d >= 2, "hp_entries: a variable that no constructor of Weight has made");
        n += v.d as usize - 1;
    }
    n
}

/// The index of the coefficient of `X_l^t` in the random coefficients (`hp_place`, hp.h:197-206).
pub fn hp_place<K: ChallengeField>(vars: &[Weight<K>], l: usize, t: usize) -> usize {
    let last = l + 1 == vars.len();
    assert!(
        l < vars.len() && t < vars[l].d as usize && (last || t >= 1),
        "hp_place: no such coefficient"
    );
    let mut at = 0usize;
    for j in 0..l {
        at += vars[j].d as usize - 1;
    }
    at + if last { t } else { t - 1 }
}

/// `U` at the challenges gamma as a linear form in the random coefficients (`hp_form`,
/// hp.h:208-223): `out[hp_place(l,t)] = gamma_l^t prod_{j>l} psi_j(gamma_j)`.
pub fn hp_form<K: ChallengeField>(vars: &[Weight<K>], gamma: &[K]) -> Vec<K> {
    assert!(
        !vars.is_empty() && gamma.len() == vars.len(),
        "hp_form: one challenge for each variable"
    );
    let mut out = vec![K::zero(); hp_entries(vars)];
    let mut tail = K::one();
    let mut l = vars.len();
    while l > 0 {
        l -= 1;
        let last = l + 1 == vars.len();
        let mut power = if last { tail } else { tail * gamma[l] };
        let mut t = if last { 0 } else { 1 };
        while t < vars[l].d as usize {
            out[hp_place(vars, l, t)] = power;
            power = power * gamma[l];
            t += 1;
        }
        tail = tail * poly_at(&vars[l].psi, gamma[l]);
    }
    out
}

/// The sumcheck of U (`HidingPolynomial`, hp.h:228-275). Call `sum()`, then `round()` and
/// `bind(challenge)` for each variable, then `value()`.
#[derive(Clone, Debug)]
pub struct HidingPolynomial<K> {
    vars: Vec<Weight<K>>,
    w: Vec<Vec<K>>,
    after: Vec<K>,
    sum: K,
    before: K,
    i: usize,
}

impl<K: ChallengeField> HidingPolynomial<K> {
    /// `entries`: `hp_entries(vars)` coefficients in the order of `hp_place()` (hp.h:231-246).
    pub fn new(vars: &[Weight<K>], entries: &[K]) -> Self {
        let k = vars.len();
        assert!(
            k >= 1 && entries.len() == hp_entries(vars),
            "HidingPolynomial: wrong number of coefficients"
        );
        let mut w = vec![vec![K::zero(); 1]; k];
        for l in 0..k {
            w[l] = vec![K::zero(); vars[l].d as usize];
            let start = if l + 1 == k { 0 } else { 1 };
            for t in start..vars[l].d as usize {
                w[l][t] = entries[hp_place(vars, l, t)];
            }
        }
        let mut after = vec![K::zero(); k];
        let mut i = k;
        while i > 1 {
            i -= 1;
            after[i - 1] = vars[i].apply(&w[i]) + vars[i].of_one() * after[i];
        }
        let sum = vars[0].apply(&w[0]) + vars[0].of_one() * after[0];
        HidingPolynomial { vars: vars.to_vec(), w, after, sum, before: K::zero(), i: 0 }
    }

    /// `(phi_1 x .. x phi_k)(U)` (`HidingPolynomial::sum`, hp.h:248).
    pub fn sum(&self) -> K {
        self.sum
    }

    /// The round polynomial of the next variable (`HidingPolynomial::round`, hp.h:251-257).
    pub fn round(&self) -> Vec<K> {
        assert!(self.i < self.vars.len(), "HidingPolynomial::round: all variables are bound");
        let mut q = self.w[self.i].clone();
        for t in 0..self.vars[self.i].psi.len() {
            q[t] = q[t] + self.before * self.vars[self.i].psi[t];
        }
        q[0] = q[0] + self.after[self.i];
        q
    }

    /// `HidingPolynomial::bind`, hp.h:258-262.
    pub fn bind(&mut self, gamma: K) {
        assert!(self.i < self.vars.len(), "HidingPolynomial::bind: all variables are bound");
        self.before = self.before * poly_at(&self.vars[self.i].psi, gamma)
            + poly_at(&self.w[self.i], gamma);
        self.i += 1;
    }

    /// U at the challenges, once all variables are bound (`HidingPolynomial::value`, hp.h:263-266).
    pub fn value(&self) -> K {
        assert_eq!(self.i, self.vars.len(), "HidingPolynomial::value: bind all variables first");
        self.before
    }
}
