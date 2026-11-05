//! `AttentionSubProof::run()` on a real `VerifierRounds`, with the test segment gate.
//!
//! The plan is the one `plan_rounds_for` builds (moments 0, 1 and 2) and the proof is a zero
//! buffer of the planned message size. The chain is already replayed against C++ in
//! `rounds_vectors.rs`; this test checks that the whole attention walk (the lookup, the eight
//! claim groups, the range check and the closing equation) runs to the end with the planned claim
//! and slot counts.

use std::rc::Rc;

use fp_core::chain::public::Binder;
use fp_core::chain::rounds::VerifierRounds;
use fp_core::chain::session::VerifierSession;
use fp_core::hash::calls::HashCalls;
use fp_core::hash::modes::Digest;
use fp_core::iop::message::Reader;
use fp_core::numbers::plan::Plan;
use fp_core::numbers::setting::Setting;
use fp_core::verifier::attention_check::{
    AttentionSubProof, AttentionSubProofInputs, OpenSegment,
};
use fp_core::verifier::attention_shape::{ACfg, AFork, Line, S_FD, S_FM, S_IX, S_RD, S_RM, S_WH, S_WL};
use fp_core::verifier::transcript::Tr;

fn config() -> ACfg {
    let mut c = ACfg::default();
    c.lt = 4;
    c.l_b = 2;
    c.lgk = 2;
    c.ldh = 2;
    c.ll = 0;
    c.s = 5;
    c.rx = 4;
    c.k_fd = 11;
    c.lm_s = 4;
    c.la = 6;
    c.lmb = 11;
    c.nmin = 10;
    c.h = 8;
    c.sh = vec![5];
    c.wc_h = 4;
    c.wc_o = 4;
    c.wc_q = 8;
    c.n_as = 2;
    c.ty = 1u128 << 18;
    c.o_in_qa = true;
    c.lines = vec![
        Line { name: String::from("KR"), kind: String::from("KR"), segs: vec![S_RM, S_RD] },
        Line { name: String::from("KF"), kind: String::from("KFD"), segs: vec![S_FM, S_FD] },
        Line { name: String::from("R"), kind: String::from("R16"), segs: vec![S_WL, S_IX] },
        Line { name: String::from("W"), kind: String::from("WH"), segs: vec![S_WH] },
    ];
    c
}

fn prover() -> AttentionSubProof {
    let mut sp = AttentionSubProof::default();
    sp.a = AFork { cf: config(), ..AFork::default() };
    sp.a.shape().unwrap();
    sp.input = AttentionSubProofInputs {
        hb: 20,
        gid: 1,
        kt_o: sp.a.fill_q / sp.a.cf.wc_q,
        col0_q: 0,
        a_o: 2,
        mid_q: 777,
        wp_s: 0,
        wp_h: 0,
        wp_o: 0,
        wp_b_a: 0,
        wp_q: 0,
        lidb: 22,
        stated_hb: 0,
        tau: 160,
    };
    sp.plan().unwrap();
    sp
}

#[test]
fn the_attention_walk_runs_to_the_end() {
    let mut sp = prover();
    let mut set = Setting::goldilocks();
    set.target = 160;
    let mut plan = Plan::new(set);
    sp.plan_rounds_for(&mut plan, 0).unwrap();
    sp.plan_rounds_for(&mut plan, 1).unwrap();
    sp.plan_rounds_for(&mut plan, 2).unwrap();
    let planned = plan.finish();
    assert!(planned.why_not.is_empty(), "the plan was refused: {}", planned.why_not);

    let n: usize = planned.rounds.iter().map(|r| r.message_bytes).sum();
    let proof = vec![0u8; n];
    let mut b = Binder::new(7, Rc::clone(&planned));
    b.configuration(&Digest::zero());
    b.no_random_bytes();
    let mut r = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    let mut gate = OpenSegment::default();
    {
        let mut ch = VerifierRounds::new(&mut b, &mut r, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            sp.run("t:", &mut tr, &mut gate, &mut calls).unwrap();
            assert!(tr.ok(), "the channel refused: {:?}", tr.why());
        }
    }
    assert_eq!(sp.n_claim as usize, sp.n_lin, "every planned claim was added");
    assert_eq!(sp.seam.tl.fold_drawn, 1, "the range check's coefficients were drawn once");
    assert_eq!(1 + sp.seam.tl.groups_run(), 2, "the two lookup groups ran");
}
