//! Replay of `scripts/cpp_vectors/layers_plan_vectors.cpp`: the plan of every layer group
//! (`vf_layers_plan.inc`), built from the fixture policy and KL.bin. The C++ tool copies that
//! file's per-group block; this test builds the same objects through `plan_layers` and compares
//! the shapes, the arrays, the counts and the placement records item by item.

use fp_core::stage_state::StageState;
use fp_core::verifier::common::tau_served;
use fp_core::verifier::layers_plan::{plan_layers, plan_sizes, reads_of, LayerPlanInputs, Reads};
use fp_core::verifier::stage_context::build_tails;
use fp_core::verifier::stage_layout::{
    layout, parse_header, pol_prescan, pol_scan, pol_skeleton, PolScan,
};
use fp_core::verifier::engine::TreeKind;
use fp_core::verifier::layers_plan::HPlan2;
use fp_core::verifier::packing::PlaceF;

const VECTORS: &str = include_str!("../../fixtures/layers_plan_vectors.txt");
const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");

fn names(v: &[String]) -> String {
    if v.is_empty() {
        String::from("-")
    } else {
        v.join(",")
    }
}

fn shp(x: &fp_core::verifier::packing::ShP) -> String {
    format!(
        "m={} k={} mS={} w={} ln={} cJ={} aX={} t={} a={} n={} mk={} p2={} k1={} kc={} j={} r={} rd={} rr={}",
        x.m, x.k, x.m_s, x.w, x.ln, x.c_j, x.a_x, x.t, x.a, x.n, x.mk, x.p2, x.k1, x.kc, x.j, x.r, x.rd, x.rr
    )
}

fn place(kind: &str, g: u64, i: usize, p: &PlaceF) -> String {
    format!(
        "LPL g={} {kind}={} owner={} rootIndex={} haveShape={} col0={} k={} m={} haveMatrix={} hb={} mS={} lanes={} padRows={} J={} K={} off={} w={} sh={}",
        g,
        i,
        p.owner,
        p.root_index,
        p.have_shape as i32,
        p.col0,
        p.k,
        p.m,
        p.have_matrix as i32,
        p.hb,
        p.m_s,
        p.lanes,
        p.pad_rows,
        p.j,
        p.kk,
        p.off,
        p.w,
        shp(&p.sh)
    )
}

fn layer_lines(plan: &HPlan2) -> Vec<String> {
    let mut out = Vec::new();
    out.push(format!(
        "LAYER g={} nU={},{},{} ns={} used={} lamS={} NCL={} nLin={} nBatched={}",
        plan.g, plan.n_u[0], plan.n_u[1], plan.n_u[2], plan.ns, plan.used, plan.lam_s, plan.n_cl, plan.n_lin,
        plan.n_batched
    ));
    for (mu, m) in plan.tl.mats.iter().enumerate() {
        out.push(format!(
            "LMAT g={} mu={} name={} m={} k={} kind={} foreign={} ttOff={} aId={} wp={}",
            plan.g, mu, m.name, m.m, m.k, m.kind, m.foreign, m.tt_off, m.a_id, m.wp
        ));
    }
    for (ti, t) in plan.fp.trees.iter().enumerate() {
        let kind = match t.kind {
            TreeKind::N => 'N',
            TreeKind::P => 'P',
        };
        out.push(format!(
            "LT g={} ti={} name={} kind={} R={} K={} owner={} rows={}",
            plan.g, ti, t.name, kind, t.r, t.k, t.owner as i32, t.rows.len()
        ));
    }
    for (ti, n) in plan.tp.nt.iter().enumerate() {
        out.push(format!(
            "LNT g={} ti={} ec={} a={} foreign={} outside={} P={} {}",
            plan.g,
            ti,
            n.ec,
            n.a,
            n.foreign as i32,
            n.outside as i32,
            n.p as i32,
            shp(&n.shape)
        ));
    }
    let ix = &plan.tl.ix;
    out.push(format!(
        "LIX g={} u={},{},{},{} tt={} bt={} zz={} yy={} kk={} bz={} tx={} ft={} pk={} count={}",
        plan.g,
        ix.u[0],
        ix.u[1],
        ix.u[2],
        ix.u[3],
        ix.tt,
        ix.bt,
        ix.zz,
        ix.yy,
        ix.kk,
        ix.bz,
        ix.tx.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
        ix.ft.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
        ix.pk.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
        ix.count
    ));
    for (i, p) in plan.tl.pl_own.iter().enumerate() {
        out.push(place("own", plan.g, i, p));
    }
    for (i, p) in plan.tl.pl_for.iter().enumerate() {
        out.push(place("for", plan.g, i, p));
    }
    out
}

fn main_lines() -> Vec<String> {
    let mut state = StageState::default();
    let mut ps = PolScan::default();
    pol_prescan(&mut ps, POLICY, &mut state).unwrap();
    pol_skeleton(&mut ps, false, &mut state).unwrap();
    pol_scan(&mut ps, POLICY, &mut state).unwrap();
    ps.h = parse_header(&ps.st, &mut state).unwrap();
    let h = &ps.h;
    // `polLayout()`'s checks and its `TAU = h.tau` (cp_verify.cpp:1184-1189).
    assert!(tau_served(h.tau as u64), "the policy's tau is not served");
    state.tau = h.tau as i32;
    assert!(
        (1..=4096).contains(&state.stated_target.hb),
        "the statement's target is out of range"
    );
    assert!(state.tau as u32 >= state.stated_target.hb, "policy-tau-hb");
    let y = layout(h, &ps.pol_calls, &state).unwrap();
    let tails = build_tails(&y, h, y.ngr);
    let p3 = h.ne > 0;
    let reads: Reads = reads_of(&y, p3);
    let sizes = plan_sizes(&y, h, &reads);
    let plans = plan_layers(&LayerPlanInputs {
        h,
        y: &y,
        tails: &tails,
        reads: &reads,
        lk_w: ps.frame.block_log,
        lidb: state.lidb,
        hb: state.stated_target.hb - state.pow as u32,
        stated_hb: state.stated_target.hb,
        limbs: state.residual_stream_limbs,
    })
    .unwrap();

    let mut out = Vec::new();
    out.push(format!(
        "STAGE ngr={} lam={} lamM={} ni={} nn={} ne={} p3={} muV={} muH={} muH2={} wW={} pow={} stated_hb={} lidb={} tau={} la={} lt={} ll={} lkW={}",
        y.ngr,
        y.lam,
        y.lam_m,
        y.ni,
        y.nn,
        h.ne,
        p3 as i32,
        sizes.mu_v,
        sizes.mu_h,
        sizes.mu_h2,
        sizes.ww,
        state.pow,
        state.stated_target.hb,
        state.lidb,
        h.tau,
        h.la,
        h.lt,
        h.ll,
        ps.frame.block_log
    ));
    out.push(format!(
        "READS tsc={} af={} qa={} xi={} xo={} ad={} ar={} qs={}",
        names(&reads.tsc_calls),
        names(&reads.af),
        names(&reads.qa),
        names(&reads.xi),
        names(&reads.xo),
        names(&reads.ad),
        names(&reads.ar),
        names(&reads.qs)
    ));
    out.push(format!("BORDER cmp={}", plans.border_cmp));
    for plan in &plans.hid {
        out.extend(layer_lines(plan));
    }
    out
}

#[test]
fn the_cpp_layer_plans_match_item_by_item() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}
