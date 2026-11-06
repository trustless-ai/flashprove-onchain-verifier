//! LINE, ported from `blocks/iop/line.h` (lines 29-41): it merges two claims on a multilinear
//! map's halves into one claim on the map.
//!
//! The C++ template over K and Ch is specialised to E and the verifier's channel.

use alloc::vec::Vec;

use super::mask::MaskTerm;
use super::summand::PointClaim;
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::R_LINE;

/// `line` (line.h:29-41). The verifier must ask the channel at the end of its run.
pub fn line(
    ch: &mut VerifierRounds<'_, '_, '_>,
    half0: PointClaim,
    half1: PointClaim,
    calls: &mut HashCalls,
) -> PointClaim {
    assert!(half0.point == half1.point, "line: the two claims must be at one point");
    let rho = {
        let mut draw = ch.close_algebraic(R_LINE, calls);
        draw.draw(calls)
    };
    let one_minus = E::one() - rho;
    let mut out = PointClaim {
        point: half0.point.clone(),
        masks: Vec::new(),
        value: one_minus * half0.value + rho * half1.value,
    };
    out.point.push(rho);
    for m in half0.masks {
        out.masks.push(MaskTerm { slot: m.slot, coeff: one_minus * m.coeff });
    }
    for m in half1.masks {
        out.masks.push(MaskTerm { slot: m.slot, coeff: rho * m.coeff });
    }
    out
}
