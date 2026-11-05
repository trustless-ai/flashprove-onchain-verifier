//! `run_layer_g()` on a real `VerifierRounds`, with the test segment gate: the plan of one layer
//! group is built by `plan_layer_moment()` from the fixture policy and KL.bin, and the proof is a
//! zero buffer of the planned message size. The walk must run to the end with the planned claim
//! and slot counts; a mismatch in the order or in a count ends at the cursor or at one of the
//! sub-proof's self-tests.


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
use fp_core::verifier::layers_check::{run_layer_g, LayerCheckInputs};
use fp_core::verifier::layers_plan::{
    plan_layer_moment, plan_layers, plan_sizes, reads_of, LayerPlanInputs, Reads,
};
use fp_core::verifier::stage_context::{build_tails, build_ws_lay};
use fp_core::verifier::stage_layout::{
    layout, parse_header, pol_prescan, pol_scan, pol_skeleton, PolScan,
};
use fp_core::verifier::transcript::Tr;

const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");
const KL_BYTES: &[u8] = include_bytes!("../../fixtures/config/KL.bin");

fn kl_words() -> Vec<u32> {
    KL_BYTES
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

#[test]
fn the_layer_walk_runs_to_the_end() {
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
    let _sizes = plan_sizes(&y, h, &reads);
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
    let ws_lay = build_ws_lay(h, &y, ps.frame.block_log).unwrap();
    let kl = kl_words();
    let plan = &plans.hid[0];
    let mut set = Setting::goldilocks();
    set.samples = ps.frame.answers;
    let mut p = Plan::new(set);
    plan_layer_moment(&mut p, plan, &y.fo, 0).unwrap();
    plan_layer_moment(&mut p, plan, &y.fo, 1).unwrap();
    plan_layer_moment(&mut p, plan, &y.fo, 2).unwrap();
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
    // The fixture has no request file; any in-range tokens run the same checks (the zero proof
    // keeps every revealed value at 0).
    let tokens: Vec<u32> = vec![0u32; y.t as usize];
    let inp = LayerCheckInputs {
        h,
        y: &y,
        plan,
        reads: &reads,
        ws_lay: &ws_lay,
        kl: &kl,
        g: 0,
        ngr: y.ngr,
        p3: h.ne > 0,
        lidb: state.lidb,
        limbs: state.residual_stream_limbs,
        gcl: state.gcl,
        rcl: state.rcl,
        tokens: &tokens,
    };
    let mut f = fp_core::verifier::engine::HFork::default();
    let mut gate = OpenSegment::default();
    {
        let mut ch = VerifierRounds::new(&mut b, &mut r, &mut session, &mut calls);
        let mut tr = Tr::new(&mut ch);
        let out = run_layer_g(&inp, &mut f, &mut tr, &mut gate, &mut calls).unwrap();
        assert!(tr.ok(), "the channel refused: {:?}", tr.why());
        assert_eq!(out.n_claim as usize, plan.n_lin, "the planned claim count");
        assert_eq!(out.n_slots, plan.ns, "the planned slot count");
    }
}
