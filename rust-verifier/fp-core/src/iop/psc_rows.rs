//! Turns PSC and LINE outputs into claims on oracle messages, ported from
//! `blocks/iop/psc_rows.h` (lines 29-83).

use alloc::boxed::Box;
use alloc::string::String;

use super::psc::PscOutput;
use super::relation::{OracleId, Part, Row};
use super::summand::PointClaim;
use super::tensor::Tensor;
use crate::field::ext::E;

/// Adds `coeff * map(point)` to `row` (`MapAt`, psc_rows.h:30).
pub type MapAt = Box<dyn Fn(&mut Row, &[E], E)>;

/// The map whose table is an aligned block of `o`'s table (`block_of_table`, psc_rows.h:40-48).
pub fn block_of_table(o: OracleId, part: Part, table_bits: u32, block: u64) -> MapAt {
    Box::new(move |row: &mut Row, point: &[E], coeff: E| {
        let a = point.len() as u32;
        assert!(
            a <= table_bits,
            "block_of_table: the point has more coordinates than the table has index bits"
        );
        let mut v = Tensor::eq(point, a, coeff);
        v.insert_choice(a, table_bits - a, block);
        row.add(o, part, v);
    })
}

/// The map whose table is row `which` of `o`'s table (`row_of_table`, psc_rows.h:51-58).
pub fn row_of_table(o: OracleId, part: Part, row_bits: u32, which: u64) -> MapAt {
    assert!(
        row_bits >= 64 || (which >> row_bits) == 0,
        "row_of_table: no such row"
    );
    Box::new(move |row: &mut Row, point: &[E], coeff: E| {
        let mut v = Tensor::eq(point, point.len() as u32, coeff);
        v.insert_choice(0, row_bits, which);
        row.add(o, part, v);
    })
}

/// PSC's claim (U) (`psc_row_u`, psc_rows.h:62-72). Moves the mask entries out of `out`.
pub fn psc_row_u(out: &mut PscOutput, kept: &[MapAt], name: impl Into<String>) -> Row {
    assert!(
        kept.len() == out.row_maps.len(),
        "psc_row_u: one MapAt for each kept map"
    );
    assert!(!out.row_masks.is_empty(), "psc_row_u: the row has been made already");
    let mut row = Row::plain(name);
    let masks = core::mem::take(&mut out.row_masks);
    for m in masks {
        row.add_mask_term(m);
    }
    for t in &out.row_maps {
        (kept[t.map as usize])(&mut row, &out.point, t.coeff);
    }
    row.target = out.row_target;
    row
}

/// `map(point) + <masks> = value` as a `Row` (`point_row`, psc_rows.h:76-83).
pub fn point_row(claim: PointClaim, map: &MapAt, name: impl Into<String>) -> Row {
    let mut row = Row::plain(name);
    map(&mut row, &claim.point, E::one());
    for m in claim.masks {
        row.add_mask_term(m);
    }
    row.target = claim.value;
    row
}
