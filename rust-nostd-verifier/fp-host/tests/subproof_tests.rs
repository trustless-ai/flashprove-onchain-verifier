//! The sub-proof machinery on a real `VerifierRounds`:
//!
//! * `HTailF2::transcript`: `Cf`'s RNG round, the commitment point, and the whole lookup on the
//!   digits (the tie, the key and table levels, the leaves and the bits), with the slot count
//!   checked by `forestPad`;
//! * `psc_begin` / `round_in` / `psc_ends` / `psc_row` on a small sumcheck;
//! * `stack_rounds`, `tsc_in`, `sc3_in` and `scd_in`.
//!
//! As `transcript_tests.rs`, the plans are built by hand and the proof is a zero buffer of the
//! planned message size: the chain's draws are deterministic and the port's `VerifierRounds` is
//! already replayed against C++ in `rounds_vectors.rs`, so these tests check the sub-proof code's
//! order, counts and return shapes, not the chain's values.

use std::rc::Rc;

use fp_core::chain::public::Binder;
use fp_core::chain::rounds::VerifierRounds;
use fp_core::chain::session::VerifierSession;
use fp_core::field::ext::{E, F};
use fp_core::hash::calls::HashCalls;
use fp_core::hash::modes::Digest;
use fp_core::iop::message::Reader;
use fp_core::numbers::plan::{Plan, PlanRound, Planned};
use fp_core::numbers::round_names::{
    R_PSC_EPSILON, R_PSC_ROUND, R_PSC_VALUES, R_PSC_Y,
};
use fp_core::numbers::setting::{RoundKind, Setting};
use fp_core::verifier::engine::{Aff, HFork};
use fp_core::verifier::lookup::{stack_rounds, HStack};
use fp_core::verifier::matrices::TMat;
use fp_core::verifier::segment::Tail2;
use fp_core::verifier::smallness::{HTailF2, OpenGate, T2Foreign};
use fp_core::verifier::sumcheck::{
    psc_begin, psc_begin_target, psc_ends, psc_row, round_in, sc3_in, sc3_row, scd_in, tsc_in,
    Degree3SumcheckState, RoundForm,
};
use fp_core::verifier::transcript::Tr;

fn setting(tau: u32) -> Setting {
    let mut set = Setting::goldilocks();
    set.target = tau;
    set
}

fn planned(set: Setting, rounds: Vec<PlanRound>) -> Rc<Planned> {
    Rc::new(Planned::new(set, rounds, Vec::new(), Vec::new(), String::new()))
}

fn zero_proof(planned: &Planned) -> Vec<u8> {
    let n: usize = planned.rounds.iter().map(|r| r.message_bytes as usize).sum();
    vec![0u8; n]
}

fn binder(planned: Rc<Planned>) -> Binder {
    let mut b = Binder::new(7, planned);
    b.configuration(&Digest::zero());
    b.no_random_bytes();
    b
}

fn round(name: &str, kind: RoundKind) -> PlanRound {
    let mut r = PlanRound::default();
    r.name = name.to_string();
    r.kind = kind;
    r
}

fn epsilon(bytes: usize) -> PlanRound {
    let mut r = round(R_PSC_EPSILON, RoundKind::Epsilon);
    r.message_bytes = bytes;
    r.draw_e = 1;
    r
}

fn algebraic(name: &str, bytes: usize, nonzero: bool) -> PlanRound {
    let mut r = round(name, RoundKind::Algebraic);
    r.message_bytes = bytes;
    r.draw_e = 1;
    if nonzero {
        // A nonzero draw is planned as a draw of elements that are then filtered (the chain
        // requires drawNonzero == drawE in an Algebraic round).
        r.draw_nonzero = 1;
    }
    r
}

fn values(bytes: usize) -> PlanRound {
    let mut r = round(R_PSC_VALUES, RoundKind::Empty);
    r.message_bytes = bytes;
    r
}

fn eb(v: u64) -> E {
    E::from_base(F::from_u64(v))
}

fn smallness() -> HTailF2 {
    let m0 = TMat {
        name: String::from("qa"),
        m: 10,
        k: 5,
        kind: 0,
        ..TMat::default()
    };
    let mats = vec![m0];
    let tx_of = vec![-1i32];
    let ft: Vec<T2Foreign> = Vec::new();
    let has_u = [true, true, true, false];
    let mut t = HTailF2::new();
    t.shape(&mats, &tx_of, &ft, has_u, 160, 22).unwrap();
    t.close_funs(&[]).unwrap();
    t
}

fn add_trees(t: &mut HTailF2) -> (HFork, Tail2) {
    let mut f = HFork::default();
    f.g = String::from("t:");
    f.slots(t.small_elems() as u32 + 64);
    let mut tail = Tail2::default();
    let n_u = [1u64, 1, 37];
    let a_tx: Vec<u32> = Vec::new();
    t.add_trees(&mut f, &mut tail, n_u, &a_tx, 1, 0).unwrap();
    (f, tail)
}

#[test]
fn the_smallness_transcript_runs_the_lookup() {
    let mut t = smallness();
    let (mut f, tail) = add_trees(&mut t);

    let mut plan = Plan::new(setting(160));
    t.plan_rounds(&mut plan, "smallness", 0).unwrap();
    t.plan_rounds(&mut plan, "smallness", 1).unwrap();
    let planned = plan.finish();
    assert!(planned.why_not.is_empty(), "the plan was refused: {}", planned.why_not);
    assert!(!planned.rounds.is_empty(), "the plan has rounds");

    let proof = zero_proof(&planned);
    let mut b = binder(planned);
    let mut r = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    let mut slot = 0u32;
    let mut gate = OpenGate;
    {
        let mut ch = VerifierRounds::new(&mut b, &mut r, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            t.transcript(&mut f, &mut tr, &mut slot, &tail, &mut gate, &mut calls)
                .unwrap();
            assert!(tr.ok(), "the channel refused: {:?}", tr.why());
        }
    }
    assert_eq!(slot as usize, t.small_elems(), "the lookup's slot count");
    assert!(f.trees[t.ix.zz as usize].root, "ZZ is committed");
    assert!(f.trees[t.ix.bz as usize].root, "BZ is committed");
    assert_eq!(t.z[1].c.zk.len(), t.z[1].c.n as usize);
    assert_eq!(t.z[2].c.zk.len(), t.z[2].c.n as usize);
}

#[test]
fn a_sumcheck_runs_on_the_chain() {
    // pscBegin: the hiding sum, then epsilon. One EQ2 round (2 scalars). pscEnds: the Y round
    // (degree 1 in Y, 1 scalar), then one end value.
    let rounds = vec![
        epsilon(24),
        algebraic(R_PSC_ROUND, 48, false),
        algebraic(R_PSC_Y, 24, true),
        values(24),
    ];
    let planned = planned(setting(128), rounds);
    assert!(planned.why_not.is_empty(), "{}", planned.why_not);
    let proof = zero_proof(&planned);
    let mut b = binder(planned);
    let mut rd = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    let mut f = HFork::default();
    f.g = String::from("s:");
    f.slots(16);
    let mut slot = 0u32;
    {
        let mut ch = VerifierRounds::new(&mut b, &mut rd, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            let mut p =
                psc_begin(&f, &mut tr, &mut slot, &Aff::constant(eb(11)), &mut calls).unwrap();
            round_in(
                &mut f,
                &mut tr,
                &mut slot,
                RoundForm::Eq2,
                &mut p,
                eb(7),
                0,
                &mut calls,
            )
            .unwrap();
            let s_end = psc_ends(&mut f, &mut tr, &mut slot, &mut p, 1, 1, &mut calls).unwrap();
            let row = psc_row(&mut f, &mut p, eb(3), &Aff::default()).unwrap();
            assert_eq!(row.s.len(), 4, "U's coefficients for both rounds");
            assert_eq!(s_end, 4, "the end value's slot after the round slots");
            assert!(tr.ok(), "{:?}", tr.why());
        }
    }
}

#[test]
fn stack_token_and_attention_sumchecks_run() {
    // stackRounds: two SUM2 rounds (2 scalars each). tscIn: Cl and the hiding sum share the
    // epsilon round; one EQ2 round (2 scalars); the Y round (degree 1, 1 scalar); one end value.
    let rounds = vec![
        epsilon(24),
        algebraic(R_PSC_ROUND, 48, false),
        algebraic(R_PSC_ROUND, 48, false),
        epsilon(48),
        algebraic(R_PSC_ROUND, 48, false),
        algebraic(R_PSC_Y, 24, true),
        values(24),
    ];
    let planned = planned(setting(128), rounds);
    assert!(planned.why_not.is_empty(), "{}", planned.why_not);
    let proof = zero_proof(&planned);
    let mut b = binder(planned);
    let mut rd = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    let mut f = HFork::default();
    f.g = String::from("s:");
    f.slots(64);
    let mut slot = 0u32;
    {
        let mut ch = VerifierRounds::new(&mut b, &mut rd, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            let mut st = HStack { lam: 2, ..HStack::default() };
            st.p = psc_begin_target(&mut tr, &mut slot, eb(5), &mut calls).unwrap();
            st.p.started = true;
            stack_rounds(&mut f, &mut tr, &mut slot, &mut st, &mut calls).unwrap();
            assert_eq!(st.rs.len(), 2);

            let point = [eb(9)];
            let t = tsc_in(&mut f, &mut tr, &mut slot, &point, 1, 1, 1, &mut calls).unwrap();
            assert_eq!(t.r.len(), 1);
            assert!(t.s_end > t.s_cl);
            assert!(tr.ok(), "{:?}", tr.why());
        }
    }
}

#[test]
fn attention_sc3_and_scd_run() {
    // sc3In: epsilon, one SUM3 round (3 scalars), Y (degree 2, 2 scalars), 2 end values.
    // scdIn: epsilon, one NODES round of degree 2 (2 scalars), Y (degree 1), 1 end value.
    let rounds = vec![
        epsilon(24),
        algebraic(R_PSC_ROUND, 72, false),
        algebraic(R_PSC_Y, 48, true),
        values(48),
        epsilon(24),
        algebraic(R_PSC_ROUND, 48, false),
        algebraic(R_PSC_Y, 24, true),
        values(24),
    ];
    let planned = planned(setting(128), rounds);
    assert!(planned.why_not.is_empty(), "{}", planned.why_not);
    let proof = zero_proof(&planned);
    let mut b = binder(planned);
    let mut rd = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    let mut f = HFork::default();
    f.g = String::from("s:");
    f.slots(64);
    let mut slot = 0u32;
    {
        let mut ch = VerifierRounds::new(&mut b, &mut rd, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);
            let mut o: Degree3SumcheckState =
                sc3_in(&mut f, &mut tr, &mut slot, 1, 1, &Aff::constant(eb(3)), &mut calls)
                    .unwrap();
            sc3_row(&mut f, &mut o, &[eb(2)], "test").unwrap();
            let v = scd_in(
                &mut f,
                &mut tr,
                &mut slot,
                &[2],
                1,
                1,
                &Aff::constant(eb(4)),
                &mut calls,
            )
            .unwrap();
            assert_eq!(v.r.len(), 1);
            assert!(v.s_end > 0);
            assert!(tr.ok(), "{:?}", tr.why());
        }
    }
}
