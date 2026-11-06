//! The transcript adapter (`fp-core/src/verifier/transcript.rs`) on a real `VerifierRounds`.
//!
//! The plan below is built by hand, as `rounds_vectors.rs` builds its plan: one round of each
//! kind that a `tr*` wrapper closes. The proof is the concatenation of the three messages; the
//! chain's draws are deterministic and the port's `VerifierRounds` is already replayed against
//! C++ in `rounds_vectors.rs`, so this test checks the adapter's order, counts and return shapes
//! rather than the chain's values.
//!
//! Not covered here: `trAnswer`/`trPoint` under a real `BAT_SIGMA` round (the adapter rejects
//! that round before touching the channel, which is tested), and the `internal-round-name` path
//! (unreachable: `RoundName` is exhaustive). Every wrapper is exercised.

use std::rc::Rc;

use fp_core::chain::public::Binder;
use fp_core::chain::rounds::VerifierRounds;
use fp_core::chain::session::VerifierSession;
use fp_core::field::ext::{E, F};
use fp_core::field::gl64;
use fp_core::hash::calls::HashCalls;
use fp_core::hash::modes::Digest;
use fp_core::iop::message::Reader;
use fp_core::numbers::plan::{Cause, PlanRound, Planned};
use fp_core::numbers::setting::{RoundKind, Setting};
use fp_core::refusal::Refusal;
use fp_core::verifier::transcript::{
    tr_answer, tr_answer_not_zero, tr_batch, tr_batch_open, tr_batch_rows, tr_empty, tr_point,
    tr_read, tr_sum, tr_trits, RoundName, Tr,
};

fn round(name: &str, kind: RoundKind) -> PlanRound {
    let mut r = PlanRound::default();
    r.name = name.to_string();
    r.kind = kind;
    r
}

/// One round for every wrapper: message, challenge, trits, empty, point, the two batching forms.
fn plan() -> Rc<Planned> {
    let set = Setting::goldilocks();
    let mut rounds = Vec::new();

    let mut r = round("PSC epsilon", RoundKind::Epsilon);
    r.message_bytes = 24; // the hiding sum
    r.draw_e = 1;
    rounds.push(r);

    let mut r = round("PSC round", RoundKind::Algebraic);
    r.message_bytes = 24;
    r.draw_e = 1;
    rounds.push(r);

    let mut r = round("PSC Y", RoundKind::Algebraic);
    r.draw_e = 1;
    r.draw_nonzero = 1;
    rounds.push(r);

    let mut r = round("RNG", RoundKind::Bits);
    r.message_bytes = 24;
    r.draw_trits = 6;
    r.combinations = 3;
    rounds.push(r);

    rounds.push(round("LINE", RoundKind::Empty));

    let mut r = round("LKP", RoundKind::Algebraic);
    r.draw_e = 2;
    rounds.push(r);

    let mut r = round("BAT-sigma", RoundKind::Algebraic);
    r.draw_e = 1;
    r.rows = 4;
    rounds.push(r);

    let mut r = round("BAT-sigma", RoundKind::Algebraic);
    r.draw_e = 1;
    r.rows = 5;
    rounds.push(r);

    rounds.push(round("ZERO", RoundKind::Empty));

    Rc::new(Planned {
        set,
        rounds,
        messages: Vec::new(),
        parts: Vec::new(),
        cause: Cause::None,
        why_not: String::new(),
    })
}

fn binder() -> Binder {
    let mut b = Binder::new(7, plan());
    b.configuration(&Digest::zero());
    b.no_random_bytes();
    b
}

fn push_e(proof: &mut Vec<u8>, c0: u64) {
    proof.extend_from_slice(&c0.to_le_bytes());
    proof.extend_from_slice(&0u64.to_le_bytes());
    proof.extend_from_slice(&0u64.to_le_bytes());
}

fn canonical(x: &E) -> bool {
    x.0.iter().all(|f| f.0 < gl64::P)
}

#[test]
fn transcript_wrappers_follow_the_plan() {
    let mut proof = Vec::new();
    push_e(&mut proof, 11);
    push_e(&mut proof, 22);
    push_e(&mut proof, 33);

    let mut b = binder();
    let mut r = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    {
        let mut ch = VerifierRounds::new(&mut b, &mut r, &mut session, &mut calls);
        {
            let mut tr = Tr::new(&mut ch);

            assert_eq!(tr_sum(&mut tr).unwrap(), E::from_base(F(11)));
            let eps = tr_answer(&mut tr, RoundName::PscEpsilon, &mut calls).unwrap();
            assert!(canonical(&eps), "PSC epsilon challenge");

            assert_eq!(tr_read(&mut tr, 1).unwrap(), vec![E::from_base(F(22))]);
            let a = tr_answer(&mut tr, RoundName::PscRound, &mut calls).unwrap();
            assert!(canonical(&a), "PSC round challenge");

            let nz = tr_answer_not_zero(&mut tr, RoundName::PscY, &mut calls).unwrap();
            assert!(!nz.is_zero(), "PSC Y challenge");

            assert_eq!(tr_read(&mut tr, 1).unwrap(), vec![E::from_base(F(33))]);
            let t = tr_trits(&mut tr, 2, 3, &mut calls).unwrap();
            assert_eq!(t.len(), 6, "2 columns x 3 combinations");
            assert!(
                t.iter().all(|&x| (-1..=1).contains(&x)),
                "trits are in -1..=1"
            );

            tr_empty(&mut tr, RoundName::Line, &mut calls).unwrap();
            let p = tr_point(&mut tr, RoundName::Lkp, 2, &mut calls).unwrap();
            assert_eq!(p.len(), 2, "two LKP points");
            assert!(p.iter().all(canonical));

            let powers = tr_batch(&mut tr, 4, &mut calls).unwrap();
            assert_eq!(powers.len(), 4);
            assert_eq!(powers[0], E::one());
            for i in 1..powers.len() {
                assert_eq!(powers[i], powers[i - 1] * powers[1], "x^{}", i);
            }

            let x = tr_batch_open(&mut tr, &mut calls).unwrap();
            assert!(canonical(&x));
            tr_batch_rows(&mut tr, 5);

            tr_empty(&mut tr, RoundName::Zero, &mut calls).unwrap();

            assert!(tr.ok());
            assert_eq!(tr.why(), None);
        }
        // `finish()` also checks that the proof has no byte left over.
        assert!(ch.finish());
    }
    assert!(
        session.accepted(),
        "the channel accepted the hand-built proof"
    );
}

#[test]
fn transcript_refusals_keep_the_channel_why() {
    // No proof bytes: the first hiding sum is missing.
    let proof: Vec<u8> = Vec::new();
    let mut b = binder();
    let mut r = Reader::new(&proof);
    let mut session = VerifierSession::new();
    let mut calls = HashCalls::new();
    {
        let mut ch = VerifierRounds::new(&mut b, &mut r, &mut session, &mut calls);
        let mut tr = Tr::new(&mut ch);

        assert_eq!(tr_read(&mut tr, 1), Err(Refusal::named("chain-refused")));
        assert!(!tr.ok());
        assert!(
            tr.why().is_some(),
            "chainHeld's reason is available before the channel drops"
        );

        // The two program-fault rejections do not touch the channel.
        assert_eq!(
            tr_answer(&mut tr, RoundName::BatSigma, &mut calls),
            Err(Refusal::internal("internal-batching-bare"))
        );
        assert_eq!(
            tr_batch(&mut tr, 0, &mut calls),
            Err(Refusal::internal("internal-batching-bare"))
        );
        assert_eq!(
            tr_answer_not_zero(&mut tr, RoundName::BatSigma, &mut calls),
            Err(Refusal::internal("internal-batching-bare"))
        );
        assert_eq!(
            tr_point(&mut tr, RoundName::BatSigma, 1, &mut calls),
            Err(Refusal::internal("internal-batching-bare"))
        );
    }
    assert!(!session.accepted());
}
