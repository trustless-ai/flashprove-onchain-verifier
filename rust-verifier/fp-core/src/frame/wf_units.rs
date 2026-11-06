//! What WF looks up, derived from the row layout of the committed matrix
//! (`blocks/frame/wf_units.h`).
//!
//! The matrix's cells are signed bytes. From row 0 on, its rows form consecutive units; the rows
//! after the last unit are single bytes. A unit of D digits and R rows stores R / D rows of
//! numbers, digit by digit: digit q of the numbers' row i is the unit's row q * (R / D) + i.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::ext::F;
use crate::frame::wf_frame::{WfShape, WfShapeLookup};
use crate::iop::wf::WfRun;

/// The widths of the range proof's two lookups (`wf_units.h:31-33`).
pub const WF_BYTE_BITS: u32 = 8;
pub const WF_WEIGHT_BITS: u32 = 13;
pub const WF_SECOND_DIGIT: u64 = 1u64 << WF_BYTE_BITS;

/// A unit of the matrix's layout (`WfUnit`, wf_units.h:23-26).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WfUnit {
    pub first_row: u64,
    pub rows: u64,
    pub digits: u32,
}

/// `wf_units_fault()` (wf_units.h:37-47). For values read from a file; the first message also
/// covers a matrix of 2^40 rows or more.
pub fn wf_units_fault(matrix_rows: u64, ranged_rows: u64, units: &[WfUnit]) -> Option<&'static str> {
    if units.is_empty() || ranged_rows > matrix_rows || ranged_rows % 2 != 0 || matrix_rows >> 40 != 0
    {
        return Some("no unit, or the ranged rows are an odd number or more than the matrix has");
    }
    let mut end = 0u64;
    for u in units {
        if (u.digits != 2 && u.digits != 4) || u.rows == 0 || u.rows % u.digits as u64 != 0 {
            return Some("a unit has not two or four digits, or not the same number of rows for each");
        }
        if u.first_row < end || u.rows > ranged_rows || u.first_row > ranged_rows - u.rows {
            return Some("the units do not follow one another within the ranged rows");
        }
        if u.first_row != end {
            return Some("rows between two units belong to no entry");
        }
        end = u.first_row + u.rows;
    }
    None
}

/// `wf_shape_of_units()` (wf_units.h:65-87). Panics on a faulty list, as `BLK_REQUIRE` does; call
/// `wf_units_fault` first for units read from a file.
pub fn wf_shape_of_units(
    k_col: u32,
    matrix_rows: u64,
    ranged_rows: u64,
    units: &[WfUnit],
) -> WfShape {
    if let Some(fault) = wf_units_fault(matrix_rows, ranged_rows, units) {
        panic!("{}", fault);
    }
    let first_bound: Vec<u32> =
        if k_col >= 9 { vec![2, 1, 0, 5, 4, 3, 8, 7, 6] } else { Vec::new() };
    let mut s = WfShape { k_col, matrix_rows, lookups: Vec::new() };
    let mut bytes = WfShapeLookup::default();
    bytes.lookup.name = alloc::string::String::from("bytes");
    bytes.lookup.d = WF_BYTE_BITS;
    bytes.lookup.digit_weight = vec![F::one()];
    bytes.lookup.offset = F::from_u64(1u64 << (WF_BYTE_BITS - 1));
    bytes.lookup.first_bound = first_bound.clone();
    bytes.log_rows_apart = 1;
    let mut weights = WfShapeLookup::default();
    weights.lookup.name = alloc::string::String::from("weights");
    weights.lookup.d = WF_WEIGHT_BITS;
    weights.lookup.digit_weight = vec![F::one(), F::from_u64(WF_SECOND_DIGIT)];
    weights.lookup.offset = F::from_u64(1u64 << (WF_WEIGHT_BITS - 1));
    weights.lookup.first_bound = first_bound;
    let mut end = 0u64;
    for u in units {
        if u.digits == 2 {
            weights.entries.push(WfRun {
                first_place: 0,
                first_row: u.first_row,
                places: u.rows / 2,
                stride: u.rows / 2,
            });
        }
        end = u.first_row + u.rows;
    }
    bytes.entries = weights.entries.clone();
    for u in units {
        let h = u.rows / 4;
        let mut q = 0u64;
        while u.digits == 4 && q < 2 {
            bytes.entries.push(WfRun {
                first_place: 0,
                first_row: u.first_row + 2 * q * h,
                places: h,
                stride: h,
            });
            q += 1;
        }
    }
    let mut y = end;
    while y + 1 < ranged_rows {
        bytes.entries.push(WfRun { first_place: 0, first_row: y, places: 1, stride: 1 });
        y += 2;
    }
    s.lookups = vec![bytes, weights];
    s
}

/// `wf_layout_fault()` (wf_units.h:108-111) for a layout whose rows are all ranged.
pub fn wf_layout_fault(m0: u64, units: &[WfUnit]) -> Option<&'static str> {
    wf_units_fault(m0, m0, units)
}

/// `wf_shape_of_layout()` (wf_units.h:112-115) for a layout whose rows are all ranged.
pub fn wf_shape_of_layout(k_col: u32, m0: u64, units: &[WfUnit]) -> WfShape {
    wf_shape_of_units(k_col, m0, m0, units)
}
