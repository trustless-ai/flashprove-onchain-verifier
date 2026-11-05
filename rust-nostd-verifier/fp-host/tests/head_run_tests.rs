//! `run_head()` on a real `VerifierRounds`, with the test segment gate: the head's plan is built
//! by `plan_moment()` from the fixture policy and KL.bin, and the proof is a zero buffer of the
//! planned message size. The walk must run to the end with the planned claim and slot counts.

use fp_core::chain::public::Binder;
use fp_core::chain::rounds::VerifierRounds;
use fp_core::chain::session::VerifierSession;
use fp_core::hash::calls::HashCalls;
use fp_core::hash::modes::Digest;
use fp_core::iop::message::Reader;
use fp_core::numbers::plan::Plan;
use fp_core::numbers::setting::Setting;
use fp_core::stage_state::StageState;
use fp_core::verifier::attention_check::OpenSegment;
use fp_core::verifier::head_check::{run_head, HeadCheckInputs};
use fp_core::verifier::head_plan::plan_head;
use fp_core::verifier::layers_plan::{plan_layers, reads_of, LayerPlanInputs, Reads};
use fp_core::verifier::stage_context::{build_hl, build_tails, build_ws_lay};
use fp_core::verifier::stage_layout::{
    layout, parse_header, pol_prescan, pol_scan, pol_skeleton, PolScan,
};
use fp_core::verifier::transcript::Tr;

const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");

#[test]
fn the_head_walk_runs_to_the_end() {
    let mut state = StageState::default();
    let mut ps = PolScan::default();
    pol_prescan(&mut ps, POLICY, &mut state).unwrap();
    pol_skeleton(&mut ps, false, &mut state).unwrap();
    pol_scan(&mut ps, POLICY, &mut state).unwrap();
    ps.h = parse_header(&ps.st, &mut state).unwrap();
    let h = &ps.h;
    state.tau = h.tau as i32;
    let y = layout(h, &ps.pol_calls, &state).unwrap();
    let tails = build_tails(&y, h, y.ngr);
    let reads: Reads = reads_of(&y, h.ne > 0);
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
    let hl = build_hl(h, &y, &ps.pol_calls_h, &state).unwrap();
    let ph = plan_head(&fp_core::verifier::head_plan::HeadPlanInputs {
        h,
        y: &y,
        hl: &hl,
        hid: &plans.hid,
        lk_w: ps.frame.block_log,
        lidb: state.lidb,
        hb: state.stated_target.hb - state.pow as u32,
        stated_hb: state.stated_target.hb,
        limbs: state.residual_stream_limbs,
    })
    .unwrap();
    let ws_lay = build_ws_lay(h, &y, ps.frame.block_log).unwrap();
    let mut set = Setting::goldilocks();
    set.samples = ps.frame.answers;
    let mut p = Plan::new(set);
    ph.plan_moment(&mut p, &hl.fs, 0).unwrap();
    ph.plan_moment(&mut p, &hl.fs, 1).unwrap();
    ph.plan_moment(&mut p, &hl.fs, 2).unwrap();
    let planned = p.finish();
    assert!(planned.why_not.is_empty(), "the plan was refused: {}", planned.why_not);
    let n: usize = planned.rounds.iter().map(|r| r.message_bytes).sum();
    let proof = vec![0u8; n];
    let mut b = Binder::new(7, planned);
    b.configuration(&Digest::zero());
    b.no_random_bytes();
    let mut r = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    // The request covers every position; the tokens and y are 0 (in range).
    let t = y.t as usize;
    let win: Vec<u32> = vec![0u32; t];
    let on: Vec<bool> = vec![true; t];
    let mut on_c = vec![true; t];
    on_c[t - 1] = false;
    let hrc = (t - 1) as u64;
    let inp = HeadCheckInputs {
        h,
        y: &y,
        hl: &hl,
        plan: &ph,
        hid: &plans.hid,
        ws_lay: &ws_lay,
        ngr: y.ngr,
        lidb: state.lidb,
        limbs: state.residual_stream_limbs,
        y_tok: 0,
        win: &win,
        on: &on,
        on_c: &on_c,
        hrc,
    };
    let mut f = fp_core::verifier::engine::HFork::default();
    let mut gate = OpenSegment::default();
    {
        let mut ch = VerifierRounds::new(&mut b, &mut r, &mut session, &mut calls);
        let mut tr = Tr::new(&mut ch);
        let out = run_head(&inp, &mut f, &mut tr, &mut gate, &mut calls).unwrap();
        assert!(tr.ok(), "the channel refused: {:?}", tr.why());
        assert_eq!(out.n_claim as usize, ph.n_lin, "the planned claim count");
        assert_eq!(out.n_slots, ph.ns, "the planned slot count");
    }
}
