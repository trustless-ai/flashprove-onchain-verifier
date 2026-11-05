//! BAT, the batching of linear claims, ported from `blocks/iop/bat.h` (lines 38-152, plus the
//! verifier wrappers at 138-152). The channel is the verifier's; prover wrappers are not ported.

use alloc::string::String;

use super::relation::{
    add_to_group_row, GroupId, GroupRow, Row, RowsAside, RunInput, Statement,
};
use crate::chain::rounds::VerifierRounds;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::round_names::{R_BAT, R_BAT_SIGMA};

/// The sum of `x^i` times claim i, as one claim on group g (`Bat::combine`, bat.h:56-74).
pub fn combine(S: &Statement, g: GroupId, mut input: RunInput, x: E) -> GroupRow {
    let mut out = GroupRow { group: g, ..GroupRow::default() };
    let mut power = E::one();
    let rows = input.take_rows();
    let mut subtle = RowsAside::default();
    for r in rows {
        add_to_group_row(S, &input.layout, r, power, &mut out, Some(&mut subtle));
        power = power * x;
    }
    add_to_group_row(S, &input.layout, subtle.sums, E::one(), &mut out, None);
    out
}

/// The same sum for claims that stay on oracle messages (`Bat::combine` second form, bat.h:76-85).
pub fn combine_rows(rows: &[Row], x: E, name: impl Into<String>) -> Row {
    let mut out = Row::plain(name);
    let mut power = E::one();
    for r in rows {
        out.add_scaled(r, power);
        power = power * x;
    }
    out
}

/// BAT, the first step of a proximity test on g (`Bat::run`, bat.h:107-114).
pub fn run(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &mut Statement,
    g: GroupId,
    calls: &mut HashCalls,
) -> GroupRow {
    run_with_layout(ch, S, g, None, calls)
}

/// `Bat::run` with the optional layout output (bat.h:107-114).
pub fn run_with_layout(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &mut Statement,
    g: GroupId,
    layout: Option<&mut super::relation::GroupLayout>,
    calls: &mut HashCalls,
) -> GroupRow {
    let input = S.begin_run(g);
    let x = {
        let mut from = ch.close_algebraic(R_BAT, calls);
        from.require_rows(input.rows().len() as u64);
        from.draw(calls)
    };
    if let Some(out) = layout {
        *out = input.layout.clone();
    }
    combine(S, g, input, x)
}

/// BAT-sigma (`Bat::sigma`, bat.h:119-129).
pub fn sigma(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &Statement,
    rows: &[Row],
    name: impl Into<String>,
    calls: &mut HashCalls,
) -> Row {
    assert!(!rows.is_empty(), "bat: no rows");
    for r in rows {
        assert!(
            r.kind != super::relation::RowKind::Sample,
            "bat: a sample row stays with its oracle message until a proximity test takes it"
        );
        S.require_sampled(r);
    }
    let x = {
        let mut from = ch.close_algebraic(R_BAT_SIGMA, calls);
        from.require_rows(rows.len() as u64);
        from.draw(calls)
    };
    combine_rows(rows, x, name)
}

/// The verifier's BAT (`bat_verify`, bat.h:138-142).
pub fn bat_verify(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &mut Statement,
    g: GroupId,
    calls: &mut HashCalls,
) -> (GroupRow, bool) {
    let out = run(ch, S, g, calls);
    let ok = ch.ok();
    (out, ok)
}

/// `bat_verify` with the layout output (bat.h:138-142).
pub fn bat_verify_layout(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &mut Statement,
    g: GroupId,
    calls: &mut HashCalls,
) -> (GroupRow, super::relation::GroupLayout, bool) {
    let mut layout = super::relation::GroupLayout::default();
    let out = run_with_layout(ch, S, g, Some(&mut layout), calls);
    let ok = ch.ok();
    (out, layout, ok)
}

/// The verifier's BAT-sigma (`bat_sigma_verify`, bat.h:148-152).
pub fn bat_sigma_verify(
    ch: &mut VerifierRounds<'_, '_, '_>,
    S: &Statement,
    rows: &[Row],
    name: impl Into<String>,
    calls: &mut HashCalls,
) -> (Row, bool) {
    let out = sigma(ch, S, rows, name, calls);
    let ok = ch.ok();
    (out, ok)
}
