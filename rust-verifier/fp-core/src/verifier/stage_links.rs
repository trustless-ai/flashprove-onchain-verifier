//! The request's segments as `runStage()` builds them from the sub-proofs' plans
//! (`vf_segments.inc`, `buildLinksH`): the links, the arrays each segment declares at each commit
//! point, the layout file applied to them (`req_frame`), the request's shape and layout, the
//! sub-proofs' planner, the committer's range proof and the checks before `configure`.
//!
//! The C++ function builds `blk::Shapes` and calls `blk::configure()` itself; the port returns the
//! pieces (the caller builds `Shapes` and calls `configure`), because the port's `Shapes` owns its
//! values and `configure` takes `&dyn Fn`. Every rejection name and its order follow the C++.

use alloc::boxed::Box;
use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::frame::files::{sized, Subproofs};
use crate::frame::hiding_conditions::RangeCheck;
use crate::frame::parameters::Parameters;
use crate::frame::req_frame::{layout_read, req_frame, FrameArray, FrameLink};
use crate::frame::wf_units::{wf_shape_of_layout, wf_units_fault, WfUnit};
use crate::iop::batt::batt_masks;
use crate::iop::req_rows::{req_layout_fault, ReqLayout};
use crate::numbers::plan::Plan;
use crate::refusal::{Refusal, Result};

use super::attention_check::AttentionSubProof;
use super::common::{CE, LBZ};
use super::engine::HFork;
use super::head_plan::HPlanH2;
use super::layers_plan::{plan_layer_moment, HPlan2};
use super::lookup::HForest;
use super::segment::Tail2;
use super::segments::LinkKind;
use super::smallness::{HTailF2, T2D1, T2D0};
use super::weights_layout::WsLay;

/// One segment, as the driver dispatches it (`LinkH`).
#[derive(Clone, Debug)]
pub struct LinkMeta {
    pub name: String,
    pub gid: u32,
    pub kind: LinkKind,
    pub g: u64,
    /// Scalars the sub-proof sends.
    pub ns: u32,
    /// Has a pending claim on the weight table.
    pub fv: bool,
    /// `array_of[t]`: the segment that committed to tree t, and its name there.
    pub array_of: Vec<(usize, String)>,
}

/// What `build_links()` produces.
pub struct StageLinks {
    pub links: Vec<LinkMeta>,
    pub identifiers: Vec<u64>,
    pub range_checks: Vec<RangeCheck>,
    pub layout: ReqLayout,
    /// The request's shape, the sub-proofs' planner and the committer's range proof; `configure`
    /// takes them in a `Shapes`.
    pub sub: Subproofs,
    /// The plans the driver runs each segment with (the planner closure holds these too).
    pub hid: Rc<Vec<HPlan2>>,
    pub ah: Rc<Vec<AttentionSubProof>>,
    pub ph: Rc<HPlanH2>,
}

/// What `build_links()` reads: the plans, the stage's layout, the header numbers and the public
/// files.
pub struct BuildLinksInputs<'a> {
    pub ngr: u64,
    pub hid: Rc<Vec<HPlan2>>,
    pub ah: Rc<Vec<AttentionSubProof>>,
    pub ph: Rc<HPlanH2>,
    /// `y.fo`: the layer sub-proofs' one lookup.
    pub y_fo: &'a HForest,
    /// `HLy.fs`: the head's lookup.
    pub hl_fs: &'a HForest,
    pub ws_lay: &'a WsLay,
    /// The parameter file as `PS.frame`.
    pub frame: &'a Parameters,
    /// `layout.txt`; `None`: the configuration folder has none.
    pub layout_text: Option<&'a str>,
    /// `TAU`.
    pub tau: u64,
}

fn named(name: &str) -> Refusal {
    Refusal::named(name)
}

fn class_of(tp: &Tail2, tree: usize) -> bool {
    tp.nt[tree].ec == CE as u32
}

fn name_of(array_of: &mut [(usize, String)], tree: i32, born: usize, name: &str) -> Result<()> {
    if tree < 0 || tree as usize >= array_of.len() || !array_of[tree as usize].1.is_empty() {
        return Err(named("plan-link"));
    }
    array_of[tree as usize] = (born, String::from(name));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn own(
    array_of: &mut [(usize, String)],
    d: &mut FrameLink,
    fp: &HFork,
    tp: &Tail2,
    tree: i32,
    born: usize,
    name: &str,
) -> Result<()> {
    name_of(array_of, tree, born, name)?;
    let t = tree as usize;
    if t >= fp.trees.len() {
        return Err(named("plan-link"));
    }
    let tr = &fp.trees[t];
    let array = FrameArray {
        name: String::from(name),
        rows: tr.r,
        columns: tr.k,
        over_E: class_of(tp, t),
        life: 0,
    };
    d.moment.last_mut().unwrap().push(array);
    Ok(())
}

/// `buildLinksH()` (`vf_segments.inc:44-253`), without `configure`. Errors carry the C++ names.
pub fn build_links(inp: BuildLinksInputs<'_>) -> Result<StageLinks> {
    let ngr = inp.ngr;
    let hid = inp.hid;
    let ah = inp.ah;
    let ph = inp.ph;
    // The plans in the driver's order: G_0, A_0, G_1, A_1, ..., H.
    struct Seg<'a> {
        name: String,
        gid: u32,
        kind: LinkKind,
        g: u64,
        ns: u32,
        fv: bool,
        tl: &'a HTailF2,
        fp: &'a HFork,
        tp: &'a Tail2,
    }
    let mut segs: Vec<Seg<'_>> = Vec::new();
    for g in 0..ngr {
        let p = &hid[g as usize];
        segs.push(Seg {
            name: format!("G{}", g),
            gid: (1 + g) as u32,
            kind: LinkKind::Layers,
            g,
            ns: p.ns,
            fv: true,
            tl: &p.tl,
            fp: &p.fp,
            tp: &p.tp,
        });
        let a = &ah[g as usize];
        segs.push(Seg {
            name: format!("A{}", g),
            gid: (2 + ngr + g) as u32,
            kind: LinkKind::Attention,
            g,
            ns: a.ns,
            fv: false,
            tl: &a.seam.tl,
            fp: &a.seam.fp,
            tp: &a.seam.tp,
        });
    }
    segs.push(Seg {
        name: String::from("H"),
        gid: (1 + ngr) as u32,
        kind: LinkKind::Head,
        g: 0,
        ns: ph.ns,
        fv: true,
        tl: &ph.tl,
        fp: &ph.fp,
        tp: &ph.tp,
    });
    // Exactly one segment is the head's, and it is the last; all sub-proofs' identifiers differ.
    {
        let mut heads = 0usize;
        let mut gids: Vec<u32> = Vec::new();
        for (i, s) in segs.iter().enumerate() {
            if s.kind == LinkKind::Head {
                heads += 1;
                if i + 1 != segs.len() {
                    return Err(named("plan-head"));
                }
            }
            if gids.contains(&s.gid) {
                return Err(named("plan-link"));
            }
            gids.push(s.gid);
        }
        if heads != 1 {
            return Err(named("plan-head"));
        }
    }
    let nl = segs.len();
    if nl < 2 || nl > 64 {
        return Err(named("plan-shape"));
    }
    // The arrays each segment declares, by commit point.
    let mut array_ofs: Vec<Vec<(usize, String)>> = Vec::new();
    let mut declared: Vec<FrameLink> = Vec::new();
    for (l, s) in segs.iter().enumerate() {
        let tl = s.tl;
        let mut array_of = vec![(usize::MAX, String::new()); s.tp.nt.len()];
        let mut d = FrameLink { name: s.name.clone(), moment: vec![Vec::new()] };
        if tl.pk_mat.is_empty()
            || tl.ix.pk.len() != tl.pk_mat.len()
            || tl.ix.tx.len() != tl.px_mat.len()
            || tl.ix.ft.len() != tl.pl_for.len()
        {
            return Err(named("plan-link"));
        }
        for i in 0..tl.pk_mat.len() {
            let name = format!("M{}", tl.pk_mat[i]);
            own(&mut array_of, &mut d, s.fp, s.tp, tl.ix.pk[i], l, &name)?;
        }
        for i in 0..tl.px_mat.len() {
            let name = format!("M{}", tl.px_mat[i]);
            own(&mut array_of, &mut d, s.fp, s.tp, tl.ix.tx[i], l, &name)?;
        }
        for n in 0..4usize {
            if tl.ix.u[n] >= 0 {
                d.moment.push(Vec::new());
                let name = format!("U{}", n + 1);
                own(&mut array_of, &mut d, s.fp, s.tp, tl.ix.u[n], l, &name)?;
            }
        }
        d.moment.push(Vec::new());
        own(&mut array_of, &mut d, s.fp, s.tp, tl.ix.zz, l, "ZZ")?;
        own(&mut array_of, &mut d, s.fp, s.tp, tl.ix.bz, l, "BZ")?;
        // Matrices that an earlier sub-proof, the owner, committed to.
        for i in 0..tl.ix.ft.len() {
            let pl = &tl.pl_for[i];
            if pl.owner < 0 || pl.owner as u64 >= ngr || (2 * pl.owner as u64) >= l as u64 {
                return Err(named("plan-fold-source"));
            }
            let born = (2 * pl.owner) as usize;
            let o = &segs[born];
            let root = pl.root_index;
            if root < 0
                || (root as usize) < o.tl.pk_mat.len()
                || (root as usize) >= o.tl.pk_mat.len() + o.tl.px_mat.len()
            {
                return Err(named("plan-fold-source"));
            }
            let mu = o.tl.px_mat[root as usize - o.tl.pk_mat.len()];
            if tl.ix.ft[i] < 0 || o.tl.gt_tree[mu] as usize >= o.fp.trees.len() {
                return Err(named("plan-fold-source"));
            }
            if tl.ix.ft[i] as usize >= s.fp.trees.len() {
                return Err(named("plan-fold-source"));
            }
            let mine = &s.fp.trees[tl.ix.ft[i] as usize];
            let theirs = &o.fp.trees[o.tl.gt_tree[mu] as usize];
            if mine.r != theirs.r || mine.k != theirs.k {
                return Err(named("plan-fold-source"));
            }
            let name = format!("M{}", mu);
            name_of(&mut array_of, tl.ix.ft[i], born, &name)?;
            // Kept up to this reader: `blk::req_frame()` requires it of the layout file.
            let mut found = false;
            for a in &mut declared[born].moment[0] {
                if a.name == name {
                    a.life = core::cmp::max(a.life, (l - born) as u32);
                    found = true;
                }
            }
            if !found {
                return Err(named("plan-fold-source"));
            }
        }
        for a in &array_of {
            if a.1.is_empty() {
                return Err(named("plan-link"));
            }
        }
        array_ofs.push(array_of);
        declared.push(d);
    }
    // No default layout exists; prover/tools/pack_layout.py writes one.
    let Some(layout_text) = inp.layout_text else {
        return Err(named("plan-layout-none"));
    };
    let mut lines = Default::default();
    if let Some(_fault) = layout_read(layout_text, &mut lines) {
        return Err(named("plan-layout-read"));
    }
    let mut request = crate::iop::req::ReqShape::default();
    let mut layout = ReqLayout::default();
    if let Some(_fault) = req_frame(&declared, &lines, inp.frame.answers, &mut request, &mut layout) {
        return Err(named("plan-layout-reqframe"));
    }
    request.link.last_mut().unwrap().plain = 1; // one unmasked scalar: the next token
    let open_rows = vec![1u64; nl];
    let mut on_table = 0u64;
    for s in &segs {
        on_table += s.fv as u64;
    }
    if on_table != ngr + 1 {
        return Err(named("plan-link"));
    }
    // The sub-proofs' planner, in the driver's order.
    let kind_of: Vec<LinkKind> = segs.iter().map(|s| s.kind).collect();
    let g_of: Vec<u64> = segs.iter().map(|s| s.g).collect();
    let look = inp.y_fo.clone();
    let head_look = inp.hl_fs.clone();
    let plan_hid = Rc::clone(&hid);
    let plan_ah = Rc::clone(&ah);
    let plan_ph = Rc::clone(&ph);
    let plan: Rc<crate::iop::req::ReqSubPlan<'static>> =
        Rc::new(move |p: &mut Plan, link: usize, moment: u32, _last: &mut u64| {
            let r = match kind_of[link] {
                LinkKind::Layers => {
                    plan_layer_moment(p, &plan_hid[g_of[link] as usize], &look, moment)
                }
                LinkKind::Attention => plan_ah[g_of[link] as usize].plan_rounds_for(p, moment),
                LinkKind::Head => plan_ph.plan_moment(p, &head_look, moment),
            };
            if let Err(r) = r {
                panic!("{}", r.name());
            }
        });
    // For the committer's range proof (`wf`). Only the embedding (X = 12) may have a four-limb
    // unit, which bounds bytes and not numbers.
    for u in &inp.ws_lay.u {
        if u.nlw == 4 && u.x != 12 {
            return Err(named("internal-weight-limbs"));
        }
    }
    let units: Vec<WfUnit> = inp
        .ws_lay
        .u
        .iter()
        .map(|u| WfUnit { first_row: u.off, rows: u.rows, digits: u.nlw as u32 })
        .collect();
    if let Some(_fault) = wf_units_fault(inp.ws_lay.m0, inp.ws_lay.m0, &units) {
        return Err(named("internal-weight-limbs"));
    }
    let ranges = wf_shape_of_layout(inp.frame.block_log, inp.ws_lay.m0, &units);
    let sub = Subproofs {
        request,
        open_rows,
        plan: Some(plan),
        pending_rows: on_table,
        after_links: None,
        ranges,
    };
    let zsized = sized(inp.frame, &sub);
    if !zsized.refused.is_empty() {
        return Err(named("parameters-not-admitted"));
    }
    if let Some(fault) = req_layout_fault(&zsized.proof_codes, &zsized.request, &layout) {
        for l in 0..zsized.request.link.len() {
            let messages = &zsized.request.link[l].messages;
            for (m, message) in messages.iter().enumerate() {
                let o = &message.shape;
                let mut in_it: Vec<crate::iop::laid::LaidMatrix> = Vec::new();
                let mut names: Vec<String> = Vec::new();
                for a in &layout.link[l] {
                    if a.message == m {
                        in_it.push(a.laid.clone());
                        names.push(a.name.clone());
                    }
                }
                if in_it.is_empty() {
                    continue;
                }
                let row_bits = crate::numbers::codes::ceil_log2(o.main_rows as u64);
                let place_bits = zsized.proof_codes.base[o.code as usize].log_ell();
                if !crate::iop::laid::laid_ok(&in_it, row_bits, place_bits) {
                    return Err(named(&format!(
                        "plan-layout-diag l={} m={} names={:?} sizes={:?}",
                        l,
                        m,
                        names,
                        in_it.iter().map(|x| (x.size_i, x.size_c)).collect::<Vec<_>>()
                    )));
                }
            }
        }
        return Err(named(&format!("plan-layout-fault {}", fault)));
    }
    // The index-mask message (the pending claims' masks): a free entry for each claim and for what
    // batching them takes.
    {
        let s = &zsized.batch.input.shape;
        let ell = zsized.proof_codes.mask[s.mask_code as usize].ell as u64;
        let rows = s.mask_rows as u64;
        let answers = s.answers as u64;
        if rows == 0
            || ell < answers
            || rows * (ell - answers) + (rows - 1)
                < on_table
                    + if on_table > 1 {
                        batt_masks(zsized.batch.s.k_col()) as u64
                    } else {
                        0
                    }
        {
            return Err(named("plan-mask-row"));
        }
    }
    let mask_row = zsized.proof_codes.mask[zsized.request.mask_code as usize].ell as u64;
    for l in 0..nl {
        if segs[l].ns as u64 + zsized.request.answers as u64 > mask_row {
            return Err(named("plan-mask-row"));
        }
        for a in &array_ofs[l] {
            let Some(at) = layout.find(a.0, &a.1) else {
                return Err(named("plan-layout-array"));
            };
            let life = zsized.request.link[a.0].messages[at.message].life as u64;
            if a.0 as u64 + life < l as u64 {
                return Err(named(&format!("plan-layout-life {} {} {} {}", a.0, life, l, a.1)));
            }
        }
    }
    let identifiers: Vec<u64> = segs.iter().map(|s| s.gid as u64).collect();
    let mut range_checks = Vec::new();
    for s in &segs {
        for m in &s.tl.mats {
            range_checks.push(RangeCheck {
                rows: m.m,
                columns: m.k,
                combinations: inp.tau,
                bound: 129,
                range: 1u64 << LBZ as u32,
                digit_bits: [T2D0 as u32, T2D1 as u32],
            });
        }
    }
    let links: Vec<LinkMeta> = segs
        .iter()
        .enumerate()
        .map(|(l, s)| LinkMeta {
            name: s.name.clone(),
            gid: s.gid,
            kind: s.kind,
            g: s.g,
            ns: s.ns,
            fv: s.fv,
            array_of: array_ofs[l].clone(),
        })
        .collect();
    Ok(StageLinks { links, identifiers, range_checks, layout, sub, hid, ah, ph })
}

/// The `Shapes` a caller of `configure` builds from a `StageLinks`: the sub-proofs with their
/// planner, the layout, the identifiers and the request's range checks. `configure` calls this
/// function once; it must depend on the public files only, which the caller keeps to.
pub fn shapes_of(
    sub: Subproofs,
    layout: ReqLayout,
    identifiers: Vec<u64>,
    range_checks: Vec<RangeCheck>,
) -> crate::frame::configure::Shapes {
    crate::frame::configure::Shapes { sub, layout, identifiers, range_checks, refused: String::new() }
}
