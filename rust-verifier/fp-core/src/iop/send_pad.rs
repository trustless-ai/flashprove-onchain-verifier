//! The pad of a sample's answer, ported from `blocks/iop/send.h` (lines 119-178). SEND itself is
//! not yet ported; these are the public sizes and places that CS and FOLD read.

use alloc::vec::Vec;

use super::relation::{Codes, OracleShape, Part};
use crate::field::ext::E;
use crate::numbers::codes::ceil_log2;

/// The pad of an answer (`PadPlace`, send.h:141-146).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PadPlace {
    pub part: Part,
    pub index: u64,
    pub answer: u32,
    pub basis: E,
}

/// The cube of table bits (`SampleCube`, send.h:119-124).
#[derive(Clone, Copy, Debug, Default)]
pub struct SampleCube {
    pub has_main: bool,
    pub has_mask: bool,
    pub main_row_bits: u32,
    pub main_bits: u32,
    pub mask_row_bits: u32,
    pub mask_bits: u32,
    pub bits: u32,
}

/// `Send::cube` (send.h:150-158).
pub fn sample_cube(codes: &Codes, s: &OracleShape) -> SampleCube {
    let mut c = SampleCube {
        has_main: s.main_rows > 0,
        has_mask: s.mask_rows > 0,
        ..SampleCube::default()
    };
    if c.has_main {
        c.main_row_bits = ceil_log2(s.main_rows as u64);
        c.main_bits = c.main_row_bits + codes.base[s.code as usize].log_ell();
    }
    if c.has_mask {
        c.mask_row_bits = ceil_log2(s.mask_rows as u64);
        c.mask_bits = c.mask_row_bits + codes.mask[s.mask_code as usize].log_ell();
    }
    c.bits = if c.has_main && c.has_mask {
        core::cmp::max(c.main_bits, c.mask_bits) + 1
    } else {
        c.main_bits + c.mask_bits
    };
    c
}

/// `Send::pad` (send.h:163-178).
pub fn send_pad(codes: &Codes, s: &OracleShape) -> Vec<PadPlace> {
    let c = sample_cube(codes, s);
    let part = if c.has_mask { Part::Mask } else { Part::Main };
    let rows = if c.has_mask { s.mask_rows } else { s.main_rows };
    let row_bits = if c.has_mask { c.mask_row_bits } else { c.main_row_bits };
    let len = if c.has_mask {
        codes.mask[s.mask_code as usize].ell
    } else {
        codes.base[s.code as usize].ell
    };
    let each = if c.has_mask || s.main_deg == 3 { 1 } else { 3 };
    assert!(
        len >= each * s.answers as usize,
        "send: the row is too short for the pad"
    );
    let mut places = Vec::new();
    for i in 0..s.answers {
        for t in 0..each {
            let place = len - each * s.answers as usize + each * i as usize + t;
            places.push(PadPlace {
                part,
                index: (rows - 1) as u64 + ((place as u64) << row_bits),
                answer: i,
                basis: E::theta(t),
            });
        }
    }
    places
}

/// How many entries a message's pad holds.
pub fn send_pad_len(codes: &Codes, s: &OracleShape) -> usize {
    send_pad(codes, s).len()
}

/// `Send::free_mask_entries` (send.h:185-188).
pub fn free_mask_entries(mask_rows: usize, ell_zk: usize, answers: u32) -> u64 {
    if mask_rows == 0 || ell_zk < answers as usize {
        return 0;
    }
    mask_rows as u64 * (ell_zk as u64 - answers as u64) + (mask_rows as u64 - 1)
}

/// `Send::mask_rows_for` (send.h:190-194).
pub fn mask_rows_for(entries: u64, ell_zk: usize, answers: u32) -> usize {
    for rows in 1..=4096 {
        if free_mask_entries(rows, ell_zk, answers) >= entries {
            return rows;
        }
    }
    0
}
