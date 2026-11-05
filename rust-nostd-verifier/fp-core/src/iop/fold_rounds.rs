//! The rounds of FOLD as field arithmetic. Ported from `blocks/iop/fold_rounds.h`
//! (lines 40-175). `fold.h` adds oracle messages, hashing and bytes.
//!
//! FOLD starts from one linear claim on a group of 2^k main rows m, 2^h mask rows mu and kept
//! rows. Its summand, with a challenge eps and a hiding polynomial U, is
//! `H(X) = U(X) + eps*(<c(X),m(X)> + <d(X_1..X_h),mu(X_1..X_h)> X_{h+1}..X_k
//!               + (1-X_1)..(1-X_k) V)`.
//! It ends with one claim on the kept rows and three single rows: m folded at g_1..g_k, and mu and
//! the fresh mask each folded at g_1..g_h.

use alloc::vec;
use alloc::vec::Vec;

use super::fold_algebra::{fold_low, fold_low_once, fold_mask_table, fold_mask_variables, inner, pair_products};
use super::hp::{poly_at, ChallengeField, HidingPolynomial, Weight};

/// The hiding polynomial's 2k+1 coefficients (`fold_mask_from_coins`, fold_rounds.h:40-44).
pub fn fold_mask_from_coins<K: ChallengeField>(k: u32, coins: Vec<K>) -> Vec<K> {
    assert!(
        coins.len() == 2 * k as usize + 1,
        "fold_mask_from_coins: the number of coins is not 2k + 1"
    );
    coins
}

/// What is left of the old mask rows and of the fresh mask when FOLD ends (`FoldMaskEnd`,
/// fold_rounds.h:48-53). A row's message is what is encoded, without the random tail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldMaskEnd<K> {
    pub d: Vec<K>,
    pub mu: Vec<K>,
    pub fresh: Vec<K>,
}

/// The prover's side (`FoldProverRounds`, fold_rounds.h:58-123). It does not hold the main rows:
/// `round()` takes their unmasked polynomial as an argument.
#[derive(Clone, Debug)]
pub struct FoldProverRounds<K> {
    k: u32,
    h: u32,
    hiding: HidingPolynomial<K>,
    fresh: Vec<K>,
    d: Vec<K>,
    mu: Vec<K>,
    kept: K,
    eps: K,
    later: K,
    started: bool,
    j: u32,
    folded_inner: K,
    folded_inner_known: bool,
}

impl<K: ChallengeField> FoldProverRounds<K> {
    /// `w`: U's coefficients; `d`, `mu`: the mask rows' coefficients and messages, each 2^h rows
    /// of `len_zk` entries; `kept`: V (fold_rounds.h:64-70).
    pub fn new(k: u32, h: u32, len_zk: usize, w: &[K], d: Vec<K>, mu: Vec<K>, kept: K) -> Self {
        let hiding = HidingPolynomial::new(&fold_mask_variables::<K>(k), w);
        let fresh = fold_mask_table(k, h, len_zk, w);
        assert!(
            d.len() == (1usize << h) * len_zk && mu.len() == d.len(),
            "FOLD: the mask rows' coefficients or messages are not tables of 2^h rows"
        );
        FoldProverRounds {
            k,
            h,
            hiding,
            fresh,
            d,
            mu,
            kept,
            eps: K::zero(),
            later: K::one(),
            started: false,
            j: 0,
            folded_inner: K::zero(),
            folded_inner_known: false,
        }
    }

    pub fn mask_sum(&self) -> K {
        self.hiding.sum()
    }

    pub fn start(&mut self, eps: K) {
        assert!(!self.started, "FOLD: eps was given twice");
        self.eps = eps;
        self.started = true;
    }

    /// All three coefficients of this round's polynomial, lowest first
    /// (`FoldProverRounds::round`, fold_rounds.h:76-91).
    pub fn round(&mut self, main_part: &[K]) -> Vec<K> {
        assert!(
            self.started && self.j < self.k,
            "FOLD: a round before eps or after the last variable"
        );
        assert!(
            main_part.len() == 3,
            "FOLD: the main rows' polynomial has not three coefficients"
        );
        let mut q = self.hiding.round();
        let mut mask = vec![K::zero(); 3];
        if self.j < self.h {
            mask = pair_products(&self.d, &self.mu);
        } else {
            if !self.folded_inner_known {
                self.folded_inner = inner(&self.d, &self.mu);
                self.folded_inner_known = true;
            }
            mask[1] = self.folded_inner * self.later;
        }
        for t in 0..3 {
            q[t] = q[t] + self.eps * (main_part[t] + mask[t]);
        }
        q[0] = q[0] + self.eps * self.kept;
        q[1] = q[1] - self.eps * self.kept;
        q
    }

    /// `FoldProverRounds::bind`, fold_rounds.h:92-104.
    pub fn bind(&mut self, g: K) {
        assert!(
            self.started && self.j < self.k,
            "FOLD: a challenge before eps or after the last variable"
        );
        self.hiding.bind(g);
        if self.j < self.h {
            fold_low_once(&mut self.d, &g);
            fold_low_once(&mut self.mu, &g);
            fold_low_once(&mut self.fresh, &g);
        } else {
            self.later = self.later * g;
        }
        self.kept = self.kept * (K::one() - g);
        self.j += 1;
    }

    /// `FoldProverRounds::end`, fold_rounds.h:105-112. With `with_d = false`, `d` is empty, for a
    /// caller that computes it with `fold_mask_form()`.
    pub fn end(&self, with_d: bool) -> FoldMaskEnd<K> {
        assert_eq!(self.j, self.k, "FOLD: rounds are missing");
        let mut d = if with_d { self.d.clone() } else { Vec::new() };
        let s = self.eps * self.later;
        for x in &mut d {
            *x = *x * s;
        }
        FoldMaskEnd { d, mu: self.mu.clone(), fresh: self.fresh.clone() }
    }
}

/// The verifier's side: the running claim (`FoldVerifierRounds`, fold_rounds.h:131-150).
#[derive(Clone, Debug)]
pub struct FoldVerifierRounds<K> {
    claim: K,
}

impl<K: ChallengeField> FoldVerifierRounds<K> {
    /// Starts at `mask_sum + eps * target` (fold_rounds.h:134).
    pub fn new(mask_sum: K, eps: K, target: K) -> Self {
        FoldVerifierRounds { claim: mask_sum + eps * target }
    }

    /// For a prover that does not know `target` (fold_rounds.h:137-140).
    pub fn from_first_round(q: &[K]) -> Self {
        assert_eq!(q.len(), 3, "FOLD: a round's polynomial has not three coefficients");
        FoldVerifierRounds { claim: q[0] + q[0] + q[1] + q[2] }
    }

    /// `FoldVerifierRounds::round`, fold_rounds.h:141-145.
    pub fn round(&mut self, c0: K, c2: K, g: K) {
        let mut q = vec![c0, K::zero(), c2];
        Weight::<K>::plain(3).complete(&mut q, self.claim);
        self.claim = poly_at(&q, g);
    }

    pub fn claim(&self) -> &K {
        &self.claim
    }
}

/// `FoldMaskEnd::d`, computed from the claim's d and the k challenges g (`fold_mask_form`,
/// fold_rounds.h:152-161).
pub fn fold_mask_form<K: ChallengeField>(k: u32, h: u32, d: Vec<K>, eps: K, g: &[K]) -> Vec<K> {
    assert!(
        g.len() == k as usize && h <= k,
        "fold_mask_form: more mask rows than main rows, or not one challenge for each variable"
    );
    let mut d = fold_low(d, g, h);
    let mut s = eps;
    for t in h..k {
        s = s * g[t as usize];
    }
    for x in &mut d {
        *x = *x * s;
    }
    d
}

/// The factor `eps * (1-g_1)..(1-g_k)` of the kept rows' coefficients (`fold_kept_factor`,
/// fold_rounds.h:163-175).
pub fn fold_kept_factor<K: ChallengeField>(eps: K, g: &[K]) -> K {
    let mut s = eps;
    for x in g {
        s = s * (K::one() - *x);
    }
    s
}
