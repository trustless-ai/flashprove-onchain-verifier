//! SPLIT, ported from `blocks/iop/split.h` (lines 44-115, the verifier side). It replaces a claim
//! that reads two groups by one claim on each, linked by one mask entry.

use alloc::string::String;

use super::mask::MaskSlot;
use super::relation::{GroupId, OracleId, Part, Row, RowKind, Statement};
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::R_SPLIT;

struct Halves {
    first: Row,
    second: Row,
}

fn member(S: &Statement, g: GroupId, o: OracleId) -> bool {
    S.group(g).members.contains(&o)
}

/// `Split::halve` (split.h:78-99).
fn halve(
    S: &mut Statement,
    row: &Row,
    g1: GroupId,
    g2: GroupId,
    mask_message: OracleId,
) -> Halves {
    assert!(g1 != g2, "split: two different groups");
    assert!(
        row.kind == RowKind::Plain,
        "split: only a plain row can be split, not a sample row or a generator row"
    );
    assert!(
        S.oracle(mask_message).shape.main_rows == 0,
        "split: the mask entry comes from a message with mask rows only"
    );
    assert!(
        member(S, g1, mask_message) && member(S, g2, mask_message),
        "split: the mask message is a member of both groups"
    );
    let mut h = Halves {
        first: Row::plain(String::from(&row.name) + ", first share"),
        second: Row::plain(String::from(&row.name) + ", second share"),
    };
    let side = |o: OracleId| -> bool {
        let in1 = member(S, g1, o);
        let in2 = member(S, g2, o);
        assert!(
            in1 != in2,
            "split: each oracle message of the row is a member of exactly one of the two groups"
        );
        in1
    };
    for t in &row.terms {
        if side(t.oracle) {
            h.first.terms.push(t.clone());
        } else {
            h.second.terms.push(t.clone());
        }
    }
    for u in &row.units {
        if side(u.oracle) {
            h.first.units.push(u.clone());
        } else {
            h.second.units.push(u.clone());
        }
    }
    for r in &row.runs {
        if side(r.oracle) {
            h.first.runs.push(r.clone());
        } else {
            h.second.runs.push(r.clone());
        }
    }
    for f in &row.forms {
        if side(f.oracle) {
            h.first.forms.push(f.clone());
        } else {
            h.second.forms.push(f.clone());
        }
    }
    let kappa: MaskSlot = S.masks(mask_message).take();
    h.second.add_unit(kappa.oracle(), Part::Mask, kappa.index() as u64, -E::one());
    h.first.add_mask(kappa, E::one());
    h
}

/// `Split::finish` (split.h:100-105).
fn finish(S: &mut Statement, mut h: Halves, target: E, share: E, g1: GroupId, g2: GroupId) {
    h.first.target = share;
    h.second.target = target - share;
    S.add_row(g1, h.first);
    S.add_row(g2, h.second);
}

/// The verifier's SPLIT (`Split::verify`, split.h:58-66).
pub fn split_verify(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &mut Statement,
    row: &Row,
    g1: GroupId,
    g2: GroupId,
    mask_message: OracleId,
    calls: &mut HashCalls,
) -> bool {
    let h = halve(S, row, g1, g2, mask_message);
    let mut share = E::zero();
    let good = ch.recv_e(&mut share);
    ch.close_empty(R_SPLIT, calls);
    let target = row.target;
    finish(S, h, target, share, g1, g2);
    good
}
