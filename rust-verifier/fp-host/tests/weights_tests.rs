//! `wsForkMerge` / `wsForkLin` / `wsForkEnd` and `wsPending` on a real `VerifierRounds`.

use std::rc::Rc;

use fp_core::chain::public::Binder;
use fp_core::chain::rounds::VerifierRounds;
use fp_core::chain::session::VerifierSession;
use fp_core::field::ext::{E, F};
use fp_core::hash::calls::HashCalls;
use fp_core::hash::modes::Digest;
use fp_core::iop::lin::LinShape;
use fp_core::iop::message::Reader;
use fp_core::numbers::plan::{PlanRound, Planned};
use fp_core::numbers::round_names::{R_BAT_SIGMA, R_PSC_EPSILON, R_PSC_ROUND, R_PSC_VALUES, R_PSC_Y};
use fp_core::numbers::setting::{RoundKind, Setting};
use fp_core::verifier::engine::HFork;
use fp_core::verifier::weights_layout::{
    ws_claim_shape, ws_fork_end, WsClaim, WsFac, WsLay, WsShape,
};
use fp_core::verifier::weights_merge::{ws_fork_lin, ws_fork_merge};
use fp_core::verifier::weights_pending::ws_pending;
use fp_core::verifier::transcript::Tr;

fn eb(v: u64) -> E {
    E::from_base(F::from_u64(v))
}

fn round(name: &str, kind: RoundKind) -> PlanRound {
    let mut r = PlanRound::default();
    r.name = name.to_string();
    r.kind = kind;
    r
}

fn plan(lk: i32, rows: u64) -> Rc<Planned> {
    let mut set = Setting::goldilocks();
    set.target = 128;
    let mut rounds = Vec::new();
    let mut r = round(R_BAT_SIGMA, RoundKind::Algebraic);
    r.draw_e = 1;
    r.rows = rows;
    rounds.push(r);
    let mut r = round(R_PSC_EPSILON, RoundKind::Epsilon);
    r.message_bytes = 24;
    r.draw_e = 1;
    rounds.push(r);
    for _ in 0..lk {
        let mut r = round(R_PSC_ROUND, RoundKind::Algebraic);
        r.message_bytes = 48;
        r.draw_e = 1;
        rounds.push(r);
    }
    let mut r = round(R_PSC_Y, RoundKind::Algebraic);
    r.message_bytes = 24;
    r.draw_e = 1;
    r.draw_nonzero = 1;
    rounds.push(r);
    let mut r = round(R_PSC_VALUES, RoundKind::Empty);
    r.message_bytes = 24;
    rounds.push(r);
    Rc::new(Planned::new(set, rounds, Vec::new(), Vec::new(), String::new()))
}

fn toy_layout() -> (WsLay, WsClaim) {
    let mut s = WsShape::default();
    s.dd = 32;
    s.l = 2;
    s.d = 8;
    s.dh = 4;
    s.dkv = 6;
    s.dq = 6;
    s.f = 10;
    s.fe = 12;
    s.ne = 4;
    s.v = 11;
    s.eh = 1;
    fp_core::verifier::weights_layout::ws_set_moe(&mut s, true);
    let mut lay = WsLay::default();
    lay.build(&s, 6).unwrap();
    let ui = lay.u.iter().position(|u| u.x == 12).unwrap();
    let mut f0 = WsFac::default();
    for i in 0..s.v {
        f0.av.push(eb(1000 + i));
    }
    let mut f1 = WsFac::default();
    f1.hv.push(eb(3));
    f1.pt = vec![eb(7), eb(11), eb(13)];
    let c = WsClaim { ui: ui as u32, f: vec![f0, f1] };
    ws_claim_shape(&lay, &c).unwrap();
    (lay, c)
}

fn chain(planned: Rc<Planned>, proof: &[u8]) -> (Binder, Reader<'_>, VerifierSession, HashCalls) {
    let mut b = Binder::new(7, planned);
    b.configuration(&Digest::zero());
    b.no_random_bytes();
    (b, Reader::new(proof), VerifierSession::new(), HashCalls::new())
}

#[test]
fn the_merge_and_pending_claim_run() {
    let (lay, claim) = toy_layout();
    let planned = plan(lay.lk, 1);
    assert!(planned.why_not.is_empty(), "{}", planned.why_not);
    let n: usize = planned.rounds.iter().map(|r| r.message_bytes).sum();
    let proof = vec![0u8; n];
    let (mut b, mut rd, mut session, mut calls) = chain(planned, &proof);
    let mut f = HFork::default();
    f.g = String::from("w:");
    f.slots(32);
    f.hide(0, eb(41), E::one()).unwrap();
    let mut slot = 1u32;
    let sv = [0u32];
    {
        let mut ch = VerifierRounds::new(&mut b, &mut rd, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            let (mut merged, rho) =
                ws_fork_merge(&mut f, &mut tr, &mut slot, lay.lk, &sv, &mut calls).unwrap();
            assert_eq!(rho.len(), 1);
            assert_eq!(merged.rm.len(), lay.lk as usize);
            // The sub-proof's batching element is drawn before its last claim.
            f.batch_by(eb(5)).unwrap();
            f.plan_claims = 1;
            f.kap_map = vec![false; 1];
            ws_fork_lin(&mut f, &mut merged).unwrap();
            assert_eq!(f.n_claim, 1);
            assert!(tr.ok(), "{:?}", tr.why());
        }
    }
    {
        let planned = plan(lay.lk, 1);
        let n: usize = planned.rounds.iter().map(|r| r.message_bytes).sum();
        let proof = vec![0u8; n];
        let (mut b, mut rd, mut session, mut calls) = chain(planned, &proof);
        let mut f = HFork::default();
        f.g = String::from("w:");
        f.slots(32);
        f.hide(0, eb(41), E::one()).unwrap();
        let mut slot = 1u32;
        let mut ch = VerifierRounds::new(&mut b, &mut rd, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            let out = ws_fork_end(
                &mut f,
                &mut tr,
                &mut slot,
                &lay,
                &[claim],
                &[0u32],
                &mut calls,
            )
            .unwrap();
            assert_eq!(out.rec.len(), 1);
            let s = LinShape { matrix_rows: lay.m0, ..LinShape::default() };
            let p = ws_pending(&lay, &out, 1, &s).unwrap();
            assert_eq!(p.psi.len(), lay.lk as usize);
            assert_eq!(p.psi[0], out.merged.rm[lay.lk as usize - 1]);
            assert_eq!(p.beta, out.merged.beta);
            assert_eq!(p.target, out.merged.fvp);
            assert!(!p.g.is_empty());
            assert!(tr.ok(), "{:?}", tr.why());
        }
    }
}
