//! SEND, the verifier's side. Ported from `blocks/iop/send.h`: `SendAccess`, `SampleCube`,
//! `PadPlace`, `Send::form`, `Send::verify`, `send_verify` (send.h:93-326 and 559-564). The
//! prover's half (`send_prove`, tables, coins) is not ported.
//!
//! SEND answers an out-of-domain sample for every oracle message of a prover message: it draws a
//! seed (a point z and beta != 0), reads one answer per message, and leaves each message's sample
//! rows in the statement. `PadPlace` and the sizes live in `send_pad.rs`.

use alloc::format;
use alloc::vec::Vec;

use super::context::{receive_oracles, OracleNotice, VerifierContext};
use super::mask::{SampleReceipt, SendAccess};
use super::relation::{
    OracleId, Part, Row, RowKind, Statement,
};
use super::send_pad::{sample_cube, send_pad, SampleCube};
use crate::chain::rounds::{SampleSeed, VerifierRounds};
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::numbers::codes::ceil_log2;
use crate::numbers::round_names::{R_SEND_ANSWER, R_SEND_SEED};

pub use super::send_pad::{free_mask_entries, mask_rows_for};

/// Who closes the round of the answers (`AnswersRound`, send.h:111).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnswersRound {
    Own,
    TheCallers,
}

/// The factor that multiplies eq(., z_1 .. z_table_bits) for one table, fixing the cube's bits
/// above the table's (`Send::front`, send.h:271-279).
fn front(z: &[E], c: &SampleCube, table_bits: u32, mask: bool) -> E {
    if !(c.has_main && c.has_mask) {
        return E::one();
    }
    let mut f = if mask { z[(c.bits - 1) as usize] } else { E::one() - z[(c.bits - 1) as usize] };
    let mut t = table_bits;
    while t + 1 < c.bits {
        f = f * (E::one() - z[t as usize]);
        t += 1;
    }
    f
}

/// The linear form of `o`'s sample claim for one answer (`Send::form`, send.h:205-227).
pub fn sample_form(s: &Statement, o: OracleId, seed: &SampleSeed, answer: u32) -> Row {
    let shape = &s.oracle(o).shape;
    let c = sample_cube(s.codes(), shape);
    assert!(
        seed.z.len() >= c.bits as usize,
        "send: the seed is too short"
    );
    assert!(!(seed.beta == E::zero()), "send: beta is 0");
    let mut row = Row::plain(format!("sample of {}", shape.name));
    row.kind = RowKind::Sample;
    let on_main = if c.has_main {
        Some(super::tensor::Tensor::eq(&seed.z, c.main_bits, front(&seed.z, &c, c.main_bits, false)))
    } else {
        None
    };
    let on_mask = if c.has_mask {
        Some(super::tensor::Tensor::eq(&seed.z, c.mask_bits, front(&seed.z, &c, c.mask_bits, true)))
    } else {
        None
    };
    for p in send_pad(s.codes(), shape) {
        let under_z = match p.part {
            Part::Main => on_main.as_ref().unwrap().at(p.index),
            Part::Mask => on_mask.as_ref().unwrap().at(p.index),
        };
        let coeff = if p.answer == answer { seed.beta * p.basis } else { E::zero() };
        row.add_unit(o, p.part, p.index, coeff - under_z);
    }
    if let Some(t) = on_main {
        row.add(o, Part::Main, t);
    }
    if let Some(t) = on_mask {
        row.add(o, Part::Mask, t);
    }
    row
}

/// Those of `ids` that get answers (`Send::to_sample`, send.h:281-292).
fn to_sample(s: &Statement, ids: &[OracleId]) -> Vec<OracleId> {
    let mut todo: Vec<OracleId> = Vec::new();
    for &o in ids {
        if s.oracle(o).shape.answers > 0 {
            assert!(!s.oracle(o).sampled, "send: an oracle message is sampled once");
            assert!(
                todo.is_empty() || *todo.last().unwrap() < o,
                "send: oracle messages come in the order of sending"
            );
            todo.push(o);
        }
    }
    assert!(!todo.is_empty(), "send: nothing to sample");
    todo
}

/// The verifier's message: for each answer number, z's coordinates then beta != 0
/// (`Send::draw`, send.h:294-313).
fn draw(
    ch: &mut VerifierRounds<'_, '_, '_>,
    s: &Statement,
    todo: &[OracleId],
    calls: &mut HashCalls,
) -> Vec<SampleSeed> {
    let mut bits = 0u32;
    let mut answers = 0u32;
    for &o in todo {
        bits = core::cmp::max(bits, sample_cube(s.codes(), &s.oracle(o).shape).bits);
        answers = core::cmp::max(answers, s.oracle(o).shape.answers);
    }
    let mut seeds = Vec::new();
    {
        let mut from = ch.close_seed(R_SEND_SEED, calls);
        for i in 0..answers {
            let mut users = 0u32;
            for &o in todo {
                if s.oracle(o).shape.answers > i {
                    users += 1;
                }
            }
            seeds.push(from.seed(bits as usize, users, calls));
        }
    }
    seeds
}

/// Called when `o`'s answers are sent or read (`Send::admit`, send.h:315-325).
fn admit(s: &mut Statement, o: OracleId, rows: Vec<Row>) {
    let shape = s.oracle(o).shape.clone();
    let free_entries = if shape.mask_rows > 0 {
        free_mask_entries(
            shape.mask_rows,
            s.codes().mask[shape.mask_code as usize].ell,
            shape.answers,
        ) as u32
    } else {
        0
    };
    let places: Vec<(Part, u64)> = send_pad(s.codes(), &shape)
        .into_iter()
        .map(|p| (p.part, p.index))
        .collect();
    let rows_n = core::cmp::max(shape.mask_rows, 1) as u32;
    let log_rows = ceil_log2(shape.mask_rows as u64);
    s.sampled(
        &SendAccess,
        o,
        rows,
        places,
        SampleReceipt::new(&SendAccess, o, 0, free_entries, rows_n, log_rows),
    );
}

/// Seed and answers, for the verifier (`Send::verify`, send.h:249-269). False if an answer is
/// missing or not canonical, or if the channel had rejected before.
pub fn send_verify_answers(
    ch: &mut VerifierRounds<'_, '_, '_>,
    s: &mut Statement,
    ids: &[OracleId],
    round: AnswersRound,
    calls: &mut HashCalls,
) -> bool {
    let todo = to_sample(s, ids);
    let seeds = draw(ch, s, &todo, calls);
    let mut good = true;
    for o in todo {
        let mut rows: Vec<Row> = Vec::new();
        for i in 0..s.oracle(o).shape.answers {
            let mut row = sample_form(s, o, &seeds[i as usize], i);
            let got = ch.recv_answer(&mut row.target);
            good = got && good;
            rows.push(row);
        }
        admit(s, o, rows);
    }
    if round == AnswersRound::Own {
        ch.close_empty(R_SEND_ANSWER, calls);
    }
    good
}

/// SEND for a verifier's context (`send_verify`, send.h:556-564). Returns `(good, ids)`; on a
/// missing root the ids are those entered so far.
pub fn send_verify(
    v: &mut VerifierContext<'_, '_, '_, '_>,
    notices: &[OracleNotice],
    round: AnswersRound,
    calls: &mut HashCalls,
) -> (bool, Vec<OracleId>) {
    let mut ids = Vec::new();
    if !receive_oracles(v, notices, &mut ids) {
        return (false, ids);
    }
    let good = send_verify_answers(&mut v.ch, &mut v.st, &ids, round, calls);
    (good, ids)
}
