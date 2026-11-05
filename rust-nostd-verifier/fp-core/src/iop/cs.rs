//! CS, the code switch, ported from `blocks/iop/cs.h` (lines 44-517, the public configuration,
//! claims and `switch_rows`). The prover's drafts and the `send_verify()`/engine-dependent entry
//! points (`switch_verify`, `cs_sigma_verify`, `cs_verify`) wait for the ported SEND block; the
//! functions below are the whole public and claim side that does not read the prover's tables.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use super::bat;
use super::context::{VerifierContext, OracleNotice};
use super::relation::{
    CodeId, GroupId, GroupLayout, OracleId, OracleShape, Part, Row, RowKind, Statement, NONE_ID,
};
use super::send::{send_verify, AnswersRound};
use super::send_pad::{send_pad, PadPlace};
use super::single_rows::{group_as_run, single_rows_oracles, single_rows_read, SingleRows};
use super::tensor::{Form, Tensor};
use crate::code::code::{
    generator_at, generator_row, mask_position,
};
use crate::field::ext::{F, E};
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::numbers::round_names::{R_CS, R_LOC};
use crate::tree::positions::PositionList;

/// An aligned block of rows of one table of g (`Cut`, cs.h:51-55).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cut {
    pub part: Part,
    pub bits: u32,
    pub first_row: u64,
}

/// The oracle message that re-sends one kept member (`KeptTarget`, cs.h:68-73).
#[derive(Clone, Debug)]
pub struct KeptTarget {
    pub shape: OracleShape,
    pub leaf_class: u32,
    pub kept_again: bool,
}

/// The shape of g and where g stores the old rows' data (`SwitchTarget`, cs.h:86-92).
#[derive(Clone, Debug)]
pub struct SwitchTarget {
    pub shape: OracleShape,
    pub leaf_class: u32,
    pub main: Cut,
    pub rest: Cut,
    pub kept: Vec<KeptTarget>,
}

/// `switch_target_stage` (cs.h:96-105).
pub fn switch_target_stage(name: &str, code: CodeId, mask_code: CodeId, k: u32, h: u32, answers: u32) -> SwitchTarget {
    SwitchTarget {
        shape: OracleShape {
            name: String::from(name),
            code,
            main_rows: 1usize << k,
            main_deg: 3,
            mask_code,
            mask_rows: 1usize << h,
            answers,
        },
        leaf_class: 0,
        main: Cut { part: Part::Main, bits: k, first_row: 0 },
        rest: Cut { part: Part::Mask, bits: h, first_row: 0 },
        kept: Vec::new(),
    }
}

/// `switch_row_bits` (cs.h:108-110).
pub fn switch_row_bits(T: &SwitchTarget, part: Part) -> u32 {
    ceil_log2(if part == Part::Main { T.shape.main_rows as u64 } else { T.shape.mask_rows as u64 })
}

/// `switch_row_length` (cs.h:111-113).
pub fn switch_row_length(codes: &super::relation::Codes, T: &SwitchTarget, part: Part) -> usize {
    if part == Part::Main {
        codes.base[T.shape.code as usize].ell
    } else {
        codes.mask[T.shape.mask_code as usize].ell
    }
}

/// `cut_index` (cs.h:116-118).
pub fn cut_index(cut: &Cut, table_row_bits: u32, j: u64) -> u64 {
    (cut.first_row + (j & ((1u64 << cut.bits) - 1))) + ((j >> cut.bits) << table_row_bits)
}

/// `switch_kept` (cs.h:121-126).
pub fn switch_kept(input: &SingleRows) -> Vec<OracleId> {
    input
        .layout
        .members
        .iter()
        .enumerate()
        .filter(|(i, _)| input.layout.kept[*i])
        .map(|(_, o)| *o)
        .collect()
}

/// Where the parts of the rest begin (`SwitchParts`, cs.h:129-136).
#[derive(Clone, Debug, Default)]
pub struct SwitchParts {
    pub mask_at: Vec<usize>,
    pub main_tail_at: usize,
    pub kept_tail_at: Vec<usize>,
    pub mask_tail_at: Vec<usize>,
    pub old_pad_at: Vec<usize>,
    pub length: usize,
}

/// `switch_parts` (cs.h:137-146).
pub fn switch_parts(S: &Statement, input: &SingleRows) -> SwitchParts {
    let codes = S.codes();
    let mut p = SwitchParts::default();
    for _ in 0..input.masks {
        p.mask_at.push(p.length);
        p.length += codes.mask[input.mask_code as usize].ell;
    }
    p.main_tail_at = p.length;
    p.length += codes.base[input.code as usize].r;
    for _ in 0..input.kept_rows {
        p.kept_tail_at.push(p.length);
        p.length += codes.base[input.code as usize].r;
    }
    for _ in 0..input.masks {
        p.mask_tail_at.push(p.length);
        p.length += codes.mask[input.mask_code as usize].r;
    }
    for o in switch_kept(input) {
        p.old_pad_at.push(p.length);
        p.length += send_pad(codes, &S.oracle(o).shape).len();
    }
    p
}

/// The table indices of the rest's entries (`SwitchPlaces`, cs.h:151-176).
#[derive(Clone, Debug)]
pub struct SwitchPlaces {
    cut: Cut,
    row_bits: u32,
    pad: Vec<u64>,
    size: usize,
}

impl SwitchPlaces {
    pub fn new(codes: &super::relation::Codes, T: &SwitchTarget) -> Self {
        let cut = T.rest;
        let row_bits = switch_row_bits(T, cut.part);
        let room = (switch_row_length(codes, T, cut.part) as u64) << cut.bits;
        let mut pad = Vec::new();
        for p in send_pad(codes, &T.shape) {
            let row = p.index & ((1u64 << row_bits) - 1);
            let place = p.index >> row_bits;
            if p.part == cut.part
                && row >= cut.first_row
                && row < cut.first_row + (1u64 << cut.bits)
            {
                pad.push((row - cut.first_row) + (place << cut.bits));
            }
        }
        pad.sort_unstable();
        SwitchPlaces { cut, row_bits, size: (room - pad.len() as u64) as usize, pad }
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn at(&self, i: usize) -> u64 {
        let mut j = i as u64;
        for p in &self.pad {
            if *p <= j {
                j += 1;
            }
        }
        cut_index(&self.cut, self.row_bits, j)
    }
}

/// `switch_rest_places` (cs.h:176).
pub fn switch_rest_places(codes: &super::relation::Codes, T: &SwitchTarget) -> SwitchPlaces {
    SwitchPlaces::new(codes, T)
}

/// `switch_target_check` (cs.h:180-212).
pub fn switch_target_check(S: &Statement, input: &SingleRows, T: &SwitchTarget) {
    let codes = S.codes();
    let s = &T.shape;
    assert!(
        input.masks == 2,
        "CS: the single rows are not those that a fold leaves: a main row, the old mask row and the fresh one"
    );
    assert!(
        (input.code as usize) < codes.base.len() && (input.mask_code as usize) < codes.mask.len(),
        "CS: no such code"
    );
    assert!(
        (s.code as usize) < codes.base.len() && s.main_rows > 0 && s.main_deg == 3,
        "CS: the new oracle message needs a code, main rows, and entries in E"
    );
    assert!(s.answers >= 1, "CS: the new oracle message has no answer to its sample");
    assert!(T.main.part == Part::Main, "CS: the main row's message goes into main rows");
    assert!(
        (codes.base[input.code as usize].ell & (codes.base[input.code as usize].ell - 1)) == 0,
        "CS: the old main row's message length is no power of two"
    );
    let main_block = 1u64 << T.main.bits;
    let rest_block = 1u64 << T.rest.bits;
    assert!(
        T.main.first_row % main_block == 0 && T.rest.first_row % rest_block == 0,
        "CS: a block of rows is not aligned"
    );
    if T.rest.part == Part::Mask {
        assert!((s.mask_code as usize) < codes.mask.len(), "CS: no such code");
        assert!(
            T.main.first_row == 0
                && main_block == s.main_rows as u64
                && T.rest.first_row == 0
                && rest_block == s.mask_rows as u64,
            "CS: the two blocks are not all the rows of the new oracle message"
        );
    } else {
        assert!(
            s.mask_rows == 0
                && T.main.first_row == 0
                && T.rest.first_row == main_block
                && main_block + rest_block == s.main_rows as u64,
            "CS: the two blocks are not all the rows of the new oracle message"
        );
    }
    assert!(
        codes.base[input.code as usize].ell as u64 >= main_block
            && (codes.base[input.code as usize].ell as u64)
                <= (codes.base[s.code as usize].ell as u64) << T.main.bits,
        "CS: the main row's message does not fit its block"
    );
    assert!(
        switch_parts(S, input).length <= switch_rest_places(codes, T).size(),
        "CS: the rest does not fit its block"
    );
    let kept = switch_kept(input);
    assert!(
        T.kept.len() == kept.len(),
        "CS: one new oracle message for each kept member of the old group"
    );
    for (i, o) in kept.iter().enumerate() {
        let old = &S.oracle(*o).shape;
        let new = &T.kept[i].shape;
        assert!(
            old.mask_rows == 0 && new.mask_rows == 0,
            "CS: a kept oracle message has no mask rows"
        );
        assert!(
            (new.code as usize) < codes.base.len()
                && new.main_rows == old.main_rows
                && new.main_deg == old.main_deg
                && new.answers == old.answers
                && codes.base[new.code as usize].ell == codes.base[old.code as usize].ell,
            "CS: a kept oracle message is sent anew in the same shape"
        );
    }
}

/// `switch_lift` (cs.h:221-227).
pub fn switch_lift(mut c: Form, vars: u32, cut: &Cut, table_row_bits: u32, table_bits: u32) -> Form {
    assert!(vars >= cut.bits, "CS: the vector is shorter than one entry for each row of its block");
    let above = table_row_bits - cut.bits;
    c.insert_choice(cut.bits, above, cut.first_row >> cut.bits);
    c.insert_choice(vars + above, table_bits - (vars + above), 0);
    c
}

/// A stretch of the rest cut into equally spaced pieces (`SwitchPiece`, cs.h:233-236).
#[derive(Clone, Copy, Debug)]
pub struct SwitchPiece {
    pub from: usize,
    pub to: usize,
    pub first: u64,
    pub step: u64,
}

/// `switch_pieces` (cs.h:237-248).
pub fn switch_pieces(places: &SwitchPlaces, first: usize, count: usize) -> Vec<SwitchPiece> {
    let mut pieces = Vec::new();
    let mut i = 0usize;
    while i < count {
        let begin = places.at(first + i);
        let step = if i + 1 < count { places.at(first + i + 1) - begin } else { 1 };
        let mut end = i + 1;
        let mut last = begin;
        while end < count && places.at(first + end) == last + step {
            last += step;
            end += 1;
        }
        pieces.push(SwitchPiece { from: i, to: end, first: begin, step });
        i = end;
    }
    pieces
}

/// `switch_add_rest` over E (cs.h:251-254).
pub fn switch_add_rest_e(row: &mut Row, g: OracleId, part: Part, pieces: &[SwitchPiece], coeff: &[E]) {
    assert!(
        coeff.len() == pieces.last().map(|p| p.to).unwrap_or(0),
        "CS: not one coefficient for each entry of the stretch"
    );
    for p in pieces {
        row.add_run(g, part, p.first, p.step, coeff[p.from..p.to].to_vec());
    }
}

/// `switch_add_rest` over F (cs.h:259-262).
pub fn switch_add_rest_f(row: &mut Row, g: OracleId, part: Part, pieces: &[SwitchPiece], coeff: &Rc<Vec<F>>) {
    assert!(
        coeff.len() == pieces.last().map(|p| p.to).unwrap_or(0),
        "CS: not one coefficient for each entry of the stretch"
    );
    for p in pieces {
        row.add_run_shared(g, part, p.first, p.step, coeff.clone(), p.from, p.to - p.from);
    }
}

/// An aligned box of entries of the rest (`SwitchBox`, cs.h:268-272).
#[derive(Clone, Copy, Debug, Default)]
pub struct SwitchBox {
    pub is: bool,
    pub shift: u32,
    pub start: u64,
}

/// `switch_box` (cs.h:273-284).
pub fn switch_box(places: &SwitchPlaces, first: usize, vars: u32) -> SwitchBox {
    let mut b = SwitchBox::default();
    let count = 1usize << vars;
    if vars == 0 || first + count > places.size() {
        return b;
    }
    let step = places.at(first + 1) - places.at(first);
    if step == 0 || (step & (step - 1)) != 0 {
        return b;
    }
    for i in 1..count {
        if places.at(first + i) != places.at(first) + i as u64 * step {
            return b;
        }
    }
    b.shift = ceil_log2(step);
    b.start = places.at(first);
    b.is = ((b.start >> b.shift) & (count as u64 - 1)) == 0;
    b
}

/// `switch_on_box` (cs.h:287-291).
pub fn switch_on_box(b: &SwitchBox, mut v: Tensor, vars: u32, table_bits: u32) -> Tensor {
    v.insert_choice(0, b.shift, b.start & ((1u64 << b.shift) - 1));
    v.insert_choice(b.shift + vars, table_bits - b.shift - vars, b.start >> (b.shift + vars));
    v
}

/// `switch_add_kept` (cs.h:296-305).
pub fn switch_add_kept(
    row: &mut Row,
    pad: &[PadPlace],
    anew: OracleId,
    g: OracleId,
    rest_part: Part,
    places: &SwitchPlaces,
    old_pad_at: usize,
    c: &Form,
) {
    row.add_form(anew, c.clone());
    for (i, p) in pad.iter().enumerate() {
        let there = c.at(p.index);
        row.add_unit(anew, Part::Main, p.index, -there);
        row.add_unit(g, rest_part, places.at(old_pad_at + i), there);
    }
}

/// A claim reading only o's main table (`switch_form_on`, cs.h:309-320).
pub fn switch_form_on(o: OracleId, row: &Row) -> Form {
    let mut c = Form::default();
    let here = |oracle: OracleId, part: Part| {
        assert!(
            oracle == o && part == Part::Main,
            "CS: the sample row of a kept oracle message reads something else than its main table"
        );
    };
    for t in &row.terms {
        here(t.oracle, t.part);
        c.add(t.v.clone());
    }
    for u in &row.units {
        here(u.oracle, u.part);
        c.add_entry(u.index, u.coeff);
    }
    for r in &row.runs {
        here(r.oracle, r.part);
        for j in 0..r.size() {
            c.add_entry(r.first + r.step * j as u64, r.at(j));
        }
    }
    for f in &row.forms {
        here(f.oracle, Part::Main);
        c.add_ref(&f.c, E::one());
    }
    c
}

/// The claims that a switch makes (`switch_rows`, cs.h:376-481).
pub fn switch_rows(
    S: &Statement,
    input: &SingleRows,
    T: &SwitchTarget,
    g: OracleId,
    anew: &[OracleId],
    at: &PositionList,
    y: &[E],
) -> Vec<Row> {
    let codes = S.codes();
    assert!(
        y.len() == at.size() * input.rows(),
        "CS: one symbol for each row at each listed position"
    );
    let parts = switch_parts(S, input);
    let kept = switch_kept(input);
    assert!(
        anew.len() == kept.len(),
        "CS: one new oracle message for each kept member of the old group"
    );
    let pad: Vec<Vec<PadPlace>> = kept.iter().map(|o| send_pad(codes, &S.oracle(*o).shape)).collect();
    let places = SwitchPlaces::new(codes, T);
    let row_bits = switch_row_bits(T, Part::Main);
    let table_bits = row_bits + codes.base[T.shape.code as usize].log_ell();
    let code = codes.base[input.code as usize];
    let mut rows: Vec<Row> = Vec::new();
    let zk = codes.mask[input.mask_code as usize];
    let zk_is_a_cube = input.masks > 0 && (zk.ell & (zk.ell - 1)) == 0;
    let rest_bits = S.table_bits(g, T.rest.part);
    let mut boxes: Vec<SwitchBox> = vec![SwitchBox::default(); input.masks as usize];
    for j in 0..input.masks as usize {
        if zk_is_a_cube {
            boxes[j] = switch_box(&places, parts.mask_at[j], ceil_log2(zk.ell as u64));
        }
    }
    let main_tail = switch_pieces(&places, parts.main_tail_at, code.r);
    let mut kept_tail: Vec<Vec<SwitchPiece>> = Vec::new();
    for at_rest in &parts.kept_tail_at {
        kept_tail.push(switch_pieces(&places, *at_rest, code.r));
    }
    let mut mask_message: Vec<Vec<SwitchPiece>> = Vec::new();
    let mut mask_tail: Vec<Vec<SwitchPiece>> = Vec::new();
    for j in 0..input.masks as usize {
        mask_message.push(if boxes[j].is {
            Vec::new()
        } else {
            switch_pieces(&places, parts.mask_at[j], zk.ell)
        });
        mask_tail.push(switch_pieces(&places, parts.mask_tail_at[j], zk.r));
    }
    let sample_rows: usize = kept.iter().map(|o| S.oracle(*o).sample_rows.len()).sum();
    rows.reserve(1 + sample_rows + at.draws().len() * input.rows());

    {
        let mut old = Row::plain("claim carried through a code switch");
        old.add_form(g, switch_lift(input.c.clone(), code.log_ell(), &T.main, row_bits, table_bits));
        for f in &input.kept {
            let i = kept.iter().position(|o| *o == f.oracle).unwrap();
            switch_add_kept(&mut old, &pad[i], anew[i], g, T.rest.part, &places, parts.old_pad_at[i], &f.c);
        }
        for j in 0..input.masks as usize {
            let pieces = switch_pieces(&places, parts.mask_at[j], input.d[j].len());
            switch_add_rest_e(&mut old, g, T.rest.part, &pieces, &input.d[j]);
        }
        old.target = input.target;
        rows.push(old);
    }
    for i in 0..kept.len() {
        for sample in &S.oracle(kept[i]).sample_rows {
            let mut old = Row::plain("old sample row of a kept oracle message");
            let c = switch_form_on(kept[i], sample);
            switch_add_kept(&mut old, &pad[i], anew[i], g, T.rest.part, &places, parts.old_pad_at[i], &c);
            old.target = sample.target;
            rows.push(old);
        }
    }
    for x in at.draws() {
        let symbols = &y[at.index_of(*x) * input.rows()..];
        let finish = |gen: Row, row: usize, rows: &mut Vec<Row>| {
            let mut gen = gen;
            gen.name = String::from("generator row");
            gen.kind = RowKind::Generator;
            gen.target = symbols[row];
            rows.push(gen);
        };
        let at_x = generator_at(&code, *x);
        let mut on_message = Form::default();
        on_message.add(Tensor::product(
            &at_x.f,
            code.log_ell(),
            E([at_x.message_scale, F::zero(), F::zero()]),
        ));
        let mut tail = vec![F::zero(); code.r];
        generator_row(&code, *x, None, Some(&mut tail));
        let on_tail = Rc::new(tail);
        {
            let mut gen = Row::plain("");
            gen.add_form(g, switch_lift(on_message.clone(), code.log_ell(), &T.main, row_bits, table_bits));
            switch_add_rest_f(&mut gen, g, T.rest.part, &main_tail, &on_tail);
            finish(gen, 0, &mut rows);
        }
        let mut kept_row = 0usize;
        for i in 0..kept.len() {
            for b in 0..S.oracle(kept[i]).shape.main_rows {
                let mut gen = Row::plain("");
                let mut v = on_message.clone();
                v.insert_choice(0, S.row_bits(kept[i], Part::Main), b as u64);
                switch_add_kept(&mut gen, &pad[i], anew[i], g, T.rest.part, &places, parts.old_pad_at[i], &v);
                switch_add_rest_f(&mut gen, g, T.rest.part, &kept_tail[kept_row], &on_tail);
                finish(gen, 1 + kept_row, &mut rows);
                kept_row += 1;
            }
        }
        for j in 0..input.masks as usize {
            let x_zk = mask_position(&codes.base[input.code as usize], &zk, *x);
            let zk_message: Vec<F> = vec![F::zero(); if boxes[j].is { 0 } else { zk.ell }];
            let mut zk_tail = vec![F::zero(); zk.r];
            if boxes[j].is {
                generator_row(&zk, x_zk, None, Some(&mut zk_tail));
            } else {
                let mut m = zk_message.clone();
                generator_row(&zk, x_zk, Some(&mut m), Some(&mut zk_tail));
                let mut gen = Row::plain("");
                switch_add_rest_f(&mut gen, g, T.rest.part, &mask_message[j], &Rc::new(m));
                switch_add_rest_f(&mut gen, g, T.rest.part, &mask_tail[j], &Rc::new(zk_tail));
                finish(gen, input.mask_row(j as u32), &mut rows);
                continue;
            }
            let at_zk = generator_at(&zk, x_zk);
            let mut gen = Row::plain("");
            let t = switch_on_box(
                &boxes[j],
                Tensor::product(
                    &at_zk.f,
                    ceil_log2(zk.ell as u64),
                    E([at_zk.message_scale, F::zero(), F::zero()]),
                ),
                ceil_log2(zk.ell as u64),
                rest_bits,
            );
            gen.add(g, T.rest.part, t);
            switch_add_rest_f(&mut gen, g, T.rest.part, &mask_tail[j], &Rc::new(zk_tail));
            finish(gen, input.mask_row(j as u32), &mut rows);
        }
    }
    rows
}

/// What a switch returns (`Switched`, cs.h:484-489).
#[derive(Clone, Debug)]
pub struct Switched {
    pub g: OracleId,
    pub kept: Vec<OracleId>,
    pub with: Vec<OracleId>,
    pub at: PositionList,
}

impl Default for Switched {
    /// The C++ default is NONE_ID (cs.h:485).
    fn default() -> Self {
        Switched { g: NONE_ID, kept: Vec::new(), with: Vec::new(), at: PositionList::default() }
    }
}

/// Splits the oracle messages of the switch's prover message (`switch_sort`, cs.h:493-497).
pub fn switch_sort(ids: &[OracleId], T: &SwitchTarget, out: &mut Switched) {
    out.g = ids[0];
    out.kept = ids[1..1 + T.kept.len()].to_vec();
    out.with = ids[1 + T.kept.len()..].to_vec();
}

/// The pass-key of `switch_admit` (`SwitchAccess`, cs.h:499-507). Only this module's future
/// `switch_verify`/`switch_prove` call it.
pub struct SwitchAccess;

/// `switch_admit` (cs.h:511-517).
pub fn switch_admit(
    _: &SwitchAccess,
    S: &mut Statement,
    input: &SingleRows,
    T: &SwitchTarget,
    to: super::relation::GroupId,
    out: &Switched,
    y: &[E],
) {
    if T.shape.mask_rows > 0 {
        S.masks(out.g).close();
    }
    S.join(to, out.g, false);
    for (i, o) in out.kept.iter().enumerate() {
        S.join(to, *o, T.kept[i].kept_again);
    }
    for row in switch_rows(S, input, T, out.g, &out.kept, &out.at, y) {
        S.add_row(to, row);
    }
}

/// The oracle messages that a switch must open (`single_rows_oracles`, re-exported for callers).
pub fn switch_oracles(input: &SingleRows) -> Vec<OracleId> {
    single_rows_oracles(input)
}

/// Kept for the shape of `switch_verify`: the number of positions its channel draws.
pub fn switch_position_count(_codes: &super::relation::Codes, input: &SingleRows) -> u32 {
    _codes.base[input.code as usize].log_n
}

/// The verifier's side of `switch_prove` (`switch_verify`, cs.h:684-710).
pub fn switch_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    input: &SingleRows,
    T: &SwitchTarget,
    to: GroupId,
    with: &[OracleNotice],
    theta: Option<&mut E>,
    out: &mut Switched,
    calls: &mut HashCalls,
) -> bool {
    switch_target_check(&V.st, input, T);
    let mut notices = Vec::with_capacity(1 + T.kept.len() + with.len());
    notices.push(OracleNotice { shape: T.shape.clone(), leaf_class: T.leaf_class });
    for k in &T.kept {
        notices.push(OracleNotice { shape: k.shape.clone(), leaf_class: k.leaf_class });
    }
    notices.extend_from_slice(with);
    let (good, ids) = send_verify(V, &notices, AnswersRound::TheCallers, calls);
    if !good {
        return false;
    }
    switch_sort(&ids, T, out);

    let want_theta = theta.is_some();
    let log_n = V.st.codes().base[input.code as usize].log_n;
    let codes_run = group_as_run(V.st.codes(), input.code, input.mask_code, input.masks > 0, 0, 0, 1);
    let mut from = V.ch.close_positions(if want_theta { R_CS } else { R_LOC }, calls);
    from.require_codes(&codes_run);
    out.at = from.positions(log_n, calls);
    let theta_value = if want_theta { Some(from.batching(calls)) } else { None };
    drop(from);
    if let (Some(dst), Some(v)) = (theta, theta_value) {
        *dst = v;
    }
    if !V.ch.ok() {
        return false;
    }
    let mut y = Vec::new();
    if !single_rows_read(V, input, &out.at, &mut y, calls) {
        return false;
    }
    if V.notes.is_some() {
        let first = out.at.index_of(out.at.draws()[0]) * input.rows();
        V.note("CS: y_main at the first draw", y[first]);
        for j in 0..input.masks {
            let value = y[first + input.mask_row(j)];
            V.note(if j > 0 { "CS: y_1 at the first draw" } else { "CS: y_0 at the first draw" }, value);
        }
    }
    switch_admit(&SwitchAccess, &mut V.st, input, T, to, out, &y);
    true
}

/// `CS^sigma`, the verifier's side (`cs_sigma_verify`, cs.h:714-717).
pub fn cs_sigma_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    input: &SingleRows,
    T: &SwitchTarget,
    to: GroupId,
    with: &[OracleNotice],
    out: &mut Switched,
    calls: &mut HashCalls,
) -> bool {
    switch_verify(V, input, T, to, with, None, out, calls)
}

/// `CS`, the verifier's side (`cs_verify`, cs.h:721-730).
pub fn cs_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    input: &SingleRows,
    T: &SwitchTarget,
    to: GroupId,
    with: &[OracleNotice],
    out: &mut Switched,
    row: &mut super::relation::GroupRow,
    layout: &mut GroupLayout,
    calls: &mut HashCalls,
) -> bool {
    let mut theta = E::zero();
    if !switch_verify(V, input, T, to, with, Some(&mut theta), out, calls) {
        return false;
    }
    let run = V.st.begin_run(to);
    V.ch.require_rows(run.rows().len() as u64);
    *layout = run.layout.clone();
    *row = bat::combine(&V.st, to, run, theta);
    true
}

