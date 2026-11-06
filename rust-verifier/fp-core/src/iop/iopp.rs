//! The proximity test's public stages and checks, ported from `blocks/iop/iopp.h` (lines 40-181).
//! `iopp_verify` waits for the ported SEND block: its chain runs `cs_verify`, whose entry point
//! calls `send_verify`.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use super::base_case::{base_mask_notice, base_verify, BaseMask};
use super::bat;
use super::context::VerifierContext;
use super::cs::{cs_verify, switch_target_stage, Switched};
use super::fold::{fold_mask_notice, fold_verify, FoldMask, FoldShape};
use super::fold_algebra::fold_mask_columns;
use super::relation::{CodeId, Codes, GroupId, GroupLayout, GroupRow, Statement, NONE_ID};
use super::single_rows::SingleRows;
use crate::chain::public::{Public, PublicBytes};
use crate::code::code::{code_ok, mask_fits, CODE_MOST_LOG_N};
use crate::hash::calls::HashCalls;
use crate::iop::message::Writer;

/// 2^k main rows and 2^h mask rows (`IoppStage`, iopp.h:41-45).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IoppStage {
    pub code: CodeId,
    pub mask_code: CodeId,
    pub k: u32,
    pub h: u32,
}

impl Default for IoppStage {
    /// The C++ defaults are NONE_ID for both code numbers (iopp.h:42-44).
    fn default() -> Self {
        IoppStage { code: NONE_ID, mask_code: NONE_ID, k: 0, h: 0 }
    }
}

/// Whether the masks ride with the switch (`IoppChoice`, iopp.h:54-56).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct IoppChoice {
    pub masks_ride: bool,
}

impl PublicBytes for IoppStage {
    fn public_bytes(&self, w: &mut Writer) {
        for x in [self.code as u64, self.mask_code as u64, self.k as u64, self.h as u64] {
            w.put_u64(x);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        if self.k > CODE_MOST_LOG_N || self.h > self.k {
            Some("too many row variables, or more mask rows than main rows")
        } else {
            None
        }
    }
}

impl PublicBytes for IoppChoice {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.masks_ride as u64);
    }
}

/// `iopp_fault` (iopp.h:84-116). Returns None if the stages fit each other and the codes.
pub fn iopp_fault(codes: &Codes, st: &[IoppStage], answers: u32, stage: &mut usize) -> Option<&'static str> {
    *stage = 0;
    if st.len() < 2 {
        return Some("a proximity test has fewer than two stages");
    }
    if answers < 1 {
        return Some("the oracle message of a switch has no answer to its sample");
    }
    let power_of_two = |x: u64| x != 0 && (x & (x - 1)) == 0;
    for i in 0..st.len() {
        let s = st[i];
        *stage = i;
        if s.code as usize >= codes.base.len() || s.mask_code as usize >= codes.mask.len() {
            return Some("the stage names a code that is not there");
        }
        let c = &codes.base[s.code as usize];
        let zk = &codes.mask[s.mask_code as usize];
        if !code_ok(c) || !code_ok(zk) {
            return Some("the stage's numbers are not a code");
        }
        if !power_of_two(c.ell as u64) || !power_of_two(zk.ell as u64) {
            return Some("a message length is no power of two");
        }
        if !mask_fits(c, zk) {
            return Some("the mask code is longer than the main code");
        }
        if s.k > CODE_MOST_LOG_N || s.h > s.k {
            return Some("too many row variables, or more mask rows than main rows");
        }
        if i + 1 < st.len() {
            if s.k < 1 {
                return Some("a stage but the last has no row variable");
            }
            if zk.ell < fold_mask_columns(s.k, s.h) as usize {
                return Some("the mask rows are too short for the hiding polynomial of the fold");
            }
        } else if s.k != 0 {
            return Some("the last stage has more than one main row");
        }
        if i == 0 {
            continue;
        }
        let pc = &codes.base[st[i - 1].code as usize];
        let pzk = &codes.mask[st[i - 1].mask_code as usize];
        let room = (zk.ell as u64) << s.h;
        let carried = 2 * (pzk.ell as u64) + pc.r as u64 + 2 * (pzk.r as u64);
        if ((c.ell as u64) << s.k) != pc.ell as u64 {
            return Some("the folded main message does not fill the main rows exactly");
        }
        if room < carried + answers as u64 {
            return Some("the mask rows have no room for masks, randomness and pad");
        }
        if answers as usize > zk.ell {
            return Some("a mask row is shorter than the pad");
        }
    }
    None
}

/// The shape of a stage's FOLD (`iopp_fold_shape`, iopp.h:154-159).
/// Turns solved sizes (`Stage`, blocks/numbers/blocks.h) into stages, adding each code that the list
/// does not contain yet (`iopp_stages`, iopp.h:120-130).
pub fn iopp_stages(solved: &[crate::numbers::blocks::Stage], codes: &mut Codes) -> Vec<IoppStage> {
    fn place(list: &mut Vec<crate::code::code::Code>, c: &crate::numbers::codes::CodeSize) -> CodeId {
        let code = crate::code::code::Code {
            log_n: c.log_n,
            ell: c.ell as usize,
            r: c.r as usize,
        };
        for (i, x) in list.iter().enumerate() {
            if *x == code {
                return i as CodeId;
            }
        }
        list.push(code);
        (list.len() - 1) as CodeId
    }
    let mut st = Vec::with_capacity(solved.len());
    for s in solved {
        st.push(IoppStage {
            code: place(&mut codes.base, &s.g.main),
            mask_code: place(&mut codes.mask, &s.g.mask),
            k: s.g.k,
            h: s.g.h,
        });
    }
    st
}

/// Null, or what differs between the stages a run has and the sizes its plan was made from
/// (`iopp_sized_fault`, iopp.h:140-153).
pub fn iopp_sized_fault(
    codes: &Codes,
    stages: &[IoppStage],
    solved: &[crate::numbers::blocks::Stage],
) -> Option<&'static str> {
    if stages.len() != solved.len() {
        return Some("the proximity test is sized for another number of stages than it has");
    }
    let same = |run: &crate::code::code::Code, priced: &crate::numbers::codes::CodeSize| {
        run.log_n == priced.log_n && run.ell as u64 == priced.ell && run.r as u64 == priced.r
    };
    for i in 0..stages.len() {
        if stages[i].code as usize >= codes.base.len() || stages[i].mask_code as usize >= codes.mask.len()
        {
            return Some("a stage of the proximity test names a code that is not there");
        }
        if stages[i].k != solved[i].g.k || stages[i].h != solved[i].g.h {
            return Some("a stage of the proximity test is sized for another number of rows than it has");
        }
        if !same(&codes.base[stages[i].code as usize], &solved[i].g.main) {
            return Some("a stage of the proximity test is sized for another main code than it names");
        }
        if !same(&codes.mask[stages[i].mask_code as usize], &solved[i].g.mask) {
            return Some("a stage of the proximity test is sized for another mask code than it names");
        }
    }
    None
}

pub fn iopp_fold_shape(s: &IoppStage, mut layout: GroupLayout) -> FoldShape {
    layout.k = s.k;
    layout.h = s.h;
    FoldShape {
        code: s.code,
        mask_code: s.mask_code,
        layout,
        mask_leaf_class: 0,
        keep_folded_coefficients: false,
        folded_coefficients_alone: false,
        target_from_the_rounds: false,
    }
}

/// `iopp_first_stage_check` (iopp.h:161-164).
pub fn iopp_first_stage_check(S: &Statement, g: GroupId, L: &GroupLayout, first: &IoppStage) {
    let G = S.group(g);
    assert!(
        G.code == first.code
            && G.mask_code == first.mask_code
            && L.k == first.k
            && L.h == first.h,
        "IOPP: the first stage is not the group"
    );
}

/// The last stage as single rows (`iopp_last_rows`, iopp.h:168-181).
pub fn iopp_last_rows(s: &IoppStage, mut L: GroupLayout, row: &GroupRow) -> SingleRows {
    assert!(
        L.k == 1 && L.h == 0 && L.members.len() == 1,
        "IOPP: the last stage is one oracle message of one main and one mask row"
    );
    let zero = [E::zero()];
    let mut out = SingleRows {
        code: s.code,
        mask_code: s.mask_code,
        masks: 1,
        ..SingleRows::default()
    };
    out.c = row.c.clone();
    out.c.fix_low(&zero, 1, E::one());
    out.d.push(row.d.clone());
    out.target = row.target;
    L.k = 0;
    out.layout = L;
    out
}

use crate::field::ext::E;

/// A stage's description for callers that name it.
pub fn stage_name(s: &IoppStage) -> String {
    alloc::format!("stage {}:{} k {} h {}", s.code, s.mask_code, s.k, s.h)
}

/// `NONE_ID`, re-exported for callers that build stages.
pub const NO_STAGE: CodeId = NONE_ID;

/// The verifier's whole proximity test (`iopp_verify`, iopp.h:256-289).
pub fn iopp_verify(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    g: GroupId,
    st: &[IoppStage],
    choice: IoppChoice,
    first_mask: FoldMask,
    calls: &mut HashCalls,
) -> bool {
    let answers = V.ch.plan().set.samples;
    let mut where_ = 0usize;
    if let Some(fault) = iopp_fault(V.st.codes(), st, answers, &mut where_) {
        panic!("IOPP: {}", fault);
    }
    let (mut row, mut layout, bat_ok) = bat::bat_verify_layout(V.ch, &mut V.st, g, calls);
    if !bat_ok {
        return false;
    }
    V.note("BAT: target", row.target);
    iopp_first_stage_check(&V.st, g, &layout, &st[0]);

    let mut fold_mask = first_mask;
    let mut base_mask = BaseMask::default();
    for i in 0..st.len() - 1 {
        let mut rows = SingleRows::default();
        let carried = core::mem::take(&mut row);
        if !fold_verify(V, &iopp_fold_shape(&st[i], layout.clone()), carried, fold_mask, &mut rows, calls) {
            return false;
        }
        V.note("FOLD: target", rows.target);
        fold_mask = FoldMask::default();

        let next = st[i + 1];
        let to_last = i + 2 == st.len();
        let name = format!("stage {}", i + 2);
        let to = V.st.new_group(name.clone(), next.code, next.mask_code);
        let mut with = Vec::new();
        if choice.masks_ride {
            with.push(if to_last {
                base_mask_notice(next.code, next.mask_code, 1, 0)
            } else {
                fold_mask_notice(&iopp_fold_shape(&next, GroupLayout::default()))
            });
        }
        let mut switched = Switched::default();
        let target = switch_target_stage(&name, next.code, next.mask_code, next.k, next.h, answers);
        if !cs_verify(V, &rows, &target, to, &with, &mut switched, &mut row, &mut layout, calls) {
            return false;
        }
        V.note("CS: target", row.target);
        if V.notes.is_some() {
            V.note("CS: c'[0]", row.c.at(0));
            V.note("CS: d'[0]", *row.d.first().unwrap());
            V.note("CS: d's last entry", *row.d.last().unwrap());
        }
        if choice.masks_ride {
            if to_last {
                base_mask.sent_as(switched.with[0]);
            } else {
                fold_mask.sent_as(switched.with[0]);
            }
        }
    }
    base_verify(V, &iopp_last_rows(&st[st.len() - 1], layout, &row), base_mask, 0, calls)
}

/// The entry point whose stages and choice were bound into the chain's first query
/// (`iopp_verify(Public<..>, ..)`, iopp.h:297-300).
pub fn iopp_verify_public(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    g: GroupId,
    stages: &Public<Vec<IoppStage>>,
    choice: &Public<IoppChoice>,
    first_mask: FoldMask,
    calls: &mut HashCalls,
) -> bool {
    let st = V.ch.get(stages).clone();
    let ch = *V.ch.get(choice);
    iopp_verify(V, g, &st, ch, first_mask, calls)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use crate::numbers::blocks::{GroupSize, Stage};
    use crate::numbers::codes::{ceil_log2, CodeSize};

    fn stage(k: u32, h: u32, log_n: u32, ell: u64, r: u64) -> Stage {
        let mut g = GroupSize::default();
        g.k = k;
        g.h = h;
        g.main = CodeSize { name: String::from("m"), log_n, ell, r, over_e: true };
        g.mask = CodeSize { name: String::from("z"), log_n: log_n - 1, ell, r, over_e: true };
        Stage { g, t: 0, r_ood: 0 }
    }

    #[test]
    fn stages_place_and_dedup_their_codes() {
        let mut codes = Codes::default();
        let solved = vec![stage(2, 1, 8, 100, 10), stage(0, 0, 8, 100, 10)];
        let st = iopp_stages(&solved, &mut codes);
        assert_eq!(st.len(), 2);
        assert_eq!(st[0].code, 0);
        assert_eq!(st[1].code, 0);
        assert_eq!(st[0].mask_code, 0);
        assert_eq!(codes.base.len(), 1);
        assert_eq!(codes.mask.len(), 1);
        assert_eq!(iopp_sized_fault(&codes, &st, &solved), None);

        let mut bad = solved.clone();
        bad[0].g.k = 3;
        assert_eq!(
            iopp_sized_fault(&codes, &st, &bad),
            Some("a stage of the proximity test is sized for another number of rows than it has")
        );
        let mut bad = solved.clone();
        bad[0].g.main.r = 11;
        assert_eq!(
            iopp_sized_fault(&codes, &st, &bad),
            Some("a stage of the proximity test is sized for another main code than it names")
        );
        assert_eq!(
            iopp_sized_fault(&codes, &st[..1], &solved),
            Some("the proximity test is sized for another number of stages than it has")
        );
    }
}
