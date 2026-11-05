//! The sumcheck claim and summand, ported from `blocks/iop/summand.h` (lines 30-116).
//!
//! The port specialises the challenge field to E, the field of every message in this format. The
//! sumchecks of the C++ headers are templates over K only so that its tests can enumerate small
//! fields; the verifier always runs E.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use super::hp::Weight;
use super::mask::MaskTerm;
use crate::field::ext::E;

/// "V(point) + <masks> = value" (`PointClaim`, summand.h:36-41).
pub struct PointClaim {
    pub point: Vec<E>,
    pub masks: Vec<MaskTerm<E>>,
    pub value: E,
}

/// The claim `(phi_1 x .. x phi_k)(S) + <masks> = target` (`SumClaim`, summand.h:46-63).
pub struct SumClaim {
    pub vars: Vec<Weight<E>>,
    pub masks: Vec<MaskTerm<E>>,
    pub target: E,
}

impl SumClaim {
    /// `SumClaim::at_point` (summand.h:55-62).
    pub fn at_point(c: PointClaim, d: &[u32]) -> Self {
        assert!(d.len() == c.point.len(), "SumClaim::at_point: one degree bound for each variable");
        let mut s = SumClaim { vars: Vec::new(), masks: c.masks, target: c.value };
        for j in 0..d.len() {
            s.vars.push(Weight::equality(c.point[j], d[j]));
        }
        s
    }
}

/// The public polynomial S (`Summand`, summand.h:70-91). `at` returns (A_0, A_1, ..) for the kept
/// maps; it must cope with every shown value read from a proof without aborting.
pub struct Summand {
    pub shown: u32,
    pub kept: u32,
    pub degree: u32,
    pub at: Box<dyn Fn(&[E], &[E]) -> Vec<E>>,
}

impl Summand {
    /// S(point, y, u), computed from at() (`at_values`, summand.h:84-90).
    pub fn at_values(&self, point: &[E], y: &[E], u: &[E]) -> E {
        let a = (self.at)(point, y);
        assert!(
            a.len() == 1 + self.kept as usize && u.len() == self.kept as usize,
            "Summand: one coefficient for each kept map"
        );
        let mut r = a[0];
        for i in 0..self.kept as usize {
            r = r + a[1 + i] * u[i];
        }
        r
    }
}

/// The prover's sumcheck without masks (`SumcheckProver`, summand.h:96-110). Kept for the shape of
/// the interface; the verifier does not call it.
pub trait SumcheckProver {
    fn round(&mut self) -> Vec<E>;
    fn bind(&mut self, challenge: E);
    fn end_values(&mut self) -> Vec<E>;
}

/// The prover's copy of the mask entries (`MaskValues`, summand.h:113-114).
pub type MaskValues = Box<dyn Fn(u32, u32) -> E>;

/// An empty sum claim, for callers that build one variable at a time.
pub fn empty_claim() -> SumClaim {
    SumClaim { vars: Vec::new(), masks: Vec::new(), target: E::zero() }
}

/// A summand over one shown map, for small direct uses.
pub fn constant_summand(value: E, kept: u32) -> Summand {
    Summand {
        shown: 0,
        kept,
        degree: 0,
        at: Box::new(move |_p: &[E], _y: &[E]| {
            let mut a = vec![value];
            a.resize(1 + kept as usize, E::zero());
            a
        }),
    }
}
