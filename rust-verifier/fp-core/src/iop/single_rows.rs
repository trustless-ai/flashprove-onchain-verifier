//! The single rows between the steps of a proximity test, ported from
//! `blocks/iop/single_rows.h` (lines 37-151, the verifier-reachable data and symbols). The prover's
//! witness and engine evaluations (lines 62-72, 132-171) are not ported.

use alloc::vec;
use alloc::vec::Vec;

use super::context::{read_opened, Opened, VerifierContext};
use super::fold_algebra::fold_low;
use super::relation::{CodeId, KeptForm, OracleId, NONE_ID};
use super::tensor::Form;
use crate::code::code::Code;
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::{PricedCode, PricedGroup};
use crate::tree::positions::PositionList;

/// The statement between the steps (`SingleRows`, single_rows.h:37-57).
pub struct SingleRows {
    pub code: CodeId,
    pub mask_code: CodeId,
    pub layout: super::relation::GroupLayout,
    pub gamma: Vec<E>,
    pub masks: u32,
    pub fresh: OracleId,
    pub c: Form,
    pub kept: Vec<KeptForm>,
    pub d: Vec<Vec<E>>,
    pub target: E,
    pub kept_rows: usize,
}

impl Default for SingleRows {
    fn default() -> Self {
        SingleRows {
            code: NONE_ID,
            mask_code: NONE_ID,
            layout: Default::default(),
            gamma: Vec::new(),
            masks: 0,
            fresh: NONE_ID,
            c: Form::default(),
            kept: Vec::new(),
            d: Vec::new(),
            target: E::zero(),
            kept_rows: 0,
        }
    }
}

impl SingleRows {
    pub fn rows(&self) -> usize {
        1 + self.kept_rows + self.masks as usize
    }
    pub fn mask_row(&self, j: u32) -> usize {
        1 + self.kept_rows + j as usize
    }
}

/// `group_as_run` (single_rows.h:74-82).
pub fn group_as_run(
    codes: &super::relation::Codes,
    code: CodeId,
    mask_code: CodeId,
    with_mask: bool,
    k: u32,
    h: u32,
    slots: u64,
) -> PricedGroup {
    assert!(
        (code as usize) < codes.base.len() && (!with_mask || (mask_code as usize) < codes.mask.len()),
        "a stage names a code that does not exist"
    );
    let of = |c: &Code| PricedCode { log_n: c.log_n, ell: c.ell as u64, r: c.r as u64 };
    let mut g = PricedGroup::default();
    g.main = of(&codes.base[code as usize]);
    if with_mask {
        g.mask = of(&codes.mask[mask_code as usize]);
    }
    g.k = k;
    g.h = h;
    g.slots = slots;
    g.said = true;
    g
}

/// The oracle messages opened to read the single rows (`single_rows_oracles`, single_rows.h:85-89).
pub fn single_rows_oracles(s: &SingleRows) -> Vec<OracleId> {
    let mut ids = s.layout.members.clone();
    if s.masks == 2 {
        ids.push(s.fresh);
    }
    ids
}

/// The rows' symbols at `positions` (`single_rows_symbols`, single_rows.h:95-128).
pub fn single_rows_symbols(s: &SingleRows, opened: &Opened, positions: usize) -> Vec<E> {
    let L = &s.layout;
    assert!(
        s.gamma.len() as u32 == L.k && L.h <= L.k,
        "single rows: not one challenge for each row variable, or more mask rows than main rows"
    );
    assert!(
        L.kept.len() == L.members.len()
            && L.main_first.len() == L.members.len()
            && L.mask_first.len() == L.members.len(),
        "single rows: the layout's lists do not have one entry for each member"
    );
    assert!(
        opened.of.len() >= single_rows_oracles(s).len(),
        "single rows: opened columns of some oracle are missing"
    );
    let mut y = Vec::new();
    for i in 0..positions {
        let mut main = vec![E::zero(); 1usize << L.k];
        let mut mask = vec![E::zero(); 1usize << L.h];
        let mut kept: Vec<E> = Vec::new();
        for w in 0..L.members.len() {
            let col = &opened.of[w][i];
            assert!(
                (L.kept[w] || col.main.is_empty() || L.main_first[w] as usize + col.main.len() <= main.len())
                    && (col.mask.is_empty() || L.mask_first[w] as usize + col.mask.len() <= mask.len()),
                "single rows: a member's rows do not lie among the group's rows"
            );
            for (b, v) in col.main.iter().enumerate() {
                if L.kept[w] {
                    kept.push(*v);
                } else {
                    main[L.main_first[w] as usize + b] = *v;
                }
            }
            for (b, v) in col.mask.iter().enumerate() {
                mask[L.mask_first[w] as usize + b] = *v;
            }
        }
        assert!(
            kept.len() == s.kept_rows,
            "single rows: the number of kept rows is not the layout's"
        );
        y.push(fold_low(main, &s.gamma, L.k)[0]);
        y.extend_from_slice(&kept);
        if s.masks >= 1 {
            y.push(fold_low(mask, &s.gamma, L.h)[0]);
        }
        if s.masks == 2 {
            let fresh = &opened.of[L.members.len()][i].mask;
            assert!(
                fresh.len() == 1usize << L.h,
                "single rows: the fresh mask has not as many rows as the group has mask rows"
            );
            y.push(fold_low(fresh.clone(), &s.gamma, L.h)[0]);
        }
    }
    y
}

/// Reads the rows' openings and returns the symbols (`single_rows_read`, single_rows.h:137-143).
pub fn single_rows_read(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    s: &SingleRows,
    at: &PositionList,
    y: &mut Vec<E>,
    calls: &mut HashCalls,
) -> bool {
    if !V.ch.ok() {
        return false;
    }
    let mut opened = Opened::default();
    if !read_opened(V, &single_rows_oracles(s), at, &mut opened, calls) {
        return false;
    }
    *y = single_rows_symbols(s, &opened, at.size());
    true
}

/// `c` written out (`single_rows_main_form`, single_rows.h:147-151).
pub fn single_rows_main_form(s: &SingleRows, ell: usize) -> Vec<E> {
    let mut c = vec![E::zero(); ell];
    s.c.add_to(&mut c, ceil_log2(ell as u64));
    c
}
