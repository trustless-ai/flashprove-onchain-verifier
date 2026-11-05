//! The parts of `verifier/src/vf_segments.inc` that do not need a sub-proof's own objects: the
//! link list's shape checks (`vf_segments.inc:86-99`, `184-185`) and one sub-proof's pending claim
//! (`pendingRowH`, `vf_segments.inc:275-278`). The runners that read a layer's, an attention's or
//! the head's proof inside a segment, and `buildLinksH`'s construction of the list from their
//! plans, belong to S3 with the sub-proofs themselves.

use alloc::string::String;
use alloc::vec::Vec;

use crate::iop::lin::LinShape;
use crate::iop::member::member_pending_row;
use crate::iop::relation::{OracleId, Statement};
use crate::iop::batt::TensorRow;
use crate::refusal::Result;

use super::weights_layout::{WsForkOut, WsLay};
use super::weights_pending::ws_pending;

/// One segment's sub-proof kind (`LinkH::kind`, vf_segments.inc:20): 0 layers, 1 attention,
/// 2 the output head.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum LinkKind {
    Layers = 0,
    Attention = 1,
    Head = 2,
}

impl Default for LinkKind {
    /// The C++ member's default, `0` (vf_segments.inc:20).
    fn default() -> Self {
        LinkKind::Layers
    }
}

/// One segment of the request's chain (`LinkH`, vf_segments.inc:17-30), with what the driver
/// needs. The sub-proof's own objects (`tl`, `Fp`, `Tp`, `rounds`) stay with its runner in S3;
/// `has_rounds` records that the plan gave it rounds (the C++ `rounds` pointer is not null and the
/// function it names is not empty).
#[derive(Clone, Debug)]
pub struct LinkH {
    pub name: String,
    /// The sub-proof's public identifier.
    pub gid: u32,
    pub kind: LinkKind,
    pub g: u64,
    /// Scalars the sub-proof sends: that many entries of the segment's mask row.
    pub ns: u32,
    /// Has a pending claim: a linear claim on the weight table, tested later.
    pub fv: bool,
    pub has_rounds: bool,
    /// `array_of[t]`: the segment that commits to the sub-proof's tree t, and its name there.
    pub array_of: Vec<(usize, String)>,
}

impl Default for LinkH {
    fn default() -> Self {
        LinkH {
            name: String::new(),
            gid: 0,
            kind: LinkKind::Layers,
            g: 0,
            ns: 0,
            fv: false,
            has_rounds: false,
            array_of: Vec::new(),
        }
    }
}

/// The checks that `buildLinksH` makes on the list itself (vf_segments.inc:86-99) and on the
/// number of pending claims (vf_segments.inc:183-185). `ngr`: the number of layer groups; exactly
/// `ngr + 1` segments must have a pending claim. Null, or the refusal name that the C++ code
/// gives (`plan-head`, `plan-link`, `plan-shape`).
pub fn link_list_fault(links: &[LinkH], ngr: u64) -> Option<&'static str> {
    let mut heads = 0usize;
    let mut gids: Vec<u32> = Vec::new();
    for (i, l) in links.iter().enumerate() {
        if l.kind == LinkKind::Head {
            heads += 1;
            if i + 1 != links.len() {
                return Some("plan-head");
            }
        }
        if gids.contains(&l.gid) || !l.has_rounds {
            return Some("plan-link");
        }
        gids.push(l.gid);
    }
    if heads != 1 {
        return Some("plan-head");
    }
    let nl = links.len();
    if nl < 2 || nl > 64 {
        return Some("plan-shape");
    }
    let mut on_table = 0u64;
    for l in links {
        on_table += l.fv as u64;
    }
    if on_table != ngr + 1 {
        return Some("plan-link");
    }
    None
}

/// One sub-proof's pending claim (`pendingRowH`, vf_segments.inc:275-278): the claim on the weight
/// table, masked by the index-mask message's next free entry.
pub fn pending_row_h(
    lay: &WsLay,
    index_masks: OracleId,
    o: &WsForkOut,
    claims: usize,
    s: &LinShape,
    st: &mut Statement,
) -> Result<TensorRow> {
    let p = ws_pending(lay, o, claims, s)?;
    let c = st.masks(index_masks).take();
    Ok(member_pending_row(p.g, p.psi, c, p.beta, p.target))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn link(gid: u32, kind: LinkKind, fv: bool) -> LinkH {
        LinkH { name: String::from("L"), gid, kind, fv, has_rounds: true, ..LinkH::default() }
    }

    #[test]
    fn a_list_of_two_segments_with_one_head_at_the_end_passes() {
        let links = vec![link(1, LinkKind::Layers, true), link(2, LinkKind::Head, true)];
        assert_eq!(link_list_fault(&links, 1), None);
    }

    #[test]
    fn the_head_is_last_and_alone() {
        let links = vec![
            link(1, LinkKind::Head, true),
            link(2, LinkKind::Layers, true),
            link(3, LinkKind::Head, true),
        ];
        assert_eq!(link_list_fault(&links, 2), Some("plan-head"));
        let no_head = vec![link(1, LinkKind::Layers, true), link(2, LinkKind::Layers, true)];
        assert_eq!(link_list_fault(&no_head, 1), Some("plan-head"));
    }

    #[test]
    fn identifiers_differ_and_the_list_has_a_plannable_size() {
        let same = vec![link(1, LinkKind::Layers, true), link(1, LinkKind::Head, true)];
        assert_eq!(link_list_fault(&same, 1), Some("plan-link"));
        let one = vec![link(1, LinkKind::Head, true)];
        assert_eq!(link_list_fault(&one, 0), Some("plan-shape"));
    }

    #[test]
    fn one_pending_claim_for_each_layer_and_for_the_head() {
        let links = vec![
            link(1, LinkKind::Layers, true),
            link(2, LinkKind::Layers, true),
            link(3, LinkKind::Head, true),
        ];
        assert_eq!(link_list_fault(&links, 2), None);
        assert_eq!(link_list_fault(&links, 1), Some("plan-link"));
    }
}
