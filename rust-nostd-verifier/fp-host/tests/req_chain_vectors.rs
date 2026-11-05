//! Replay of `scripts/cpp_vectors/req_chain_vectors.cpp`: the request frame (`ReqFrame`,
//! `req_first`/`req_later`/`req_close`/`req_finish`), `ReqRows::row` (as `req_row`) and
//! `ChainCheck`/`chain_verify`, on proofs that the C++ verifier's own blocks made for the toy
//! requests of `blocks/iop/tests/req_rows_cases.h`.
//!
//! The fixture holds, per case, the codes, shape, layout, equations, plan and both proofs (as
//! bytes), and the verdicts that the C++ code reached: the honest run accepted by `chain_verify`
//! and by `ChainCheck`'s calls; a run with a spoiled weight, a proof of a false target, and runs
//! without a segment's `close()` or its last commit point all rejected. A battery of malformed
//! shapes and layouts follows, with the fault name that `req_fault()` or `req_layout_fault()`
//! returns for each; the same mutations run here, item by item.
#![allow(non_snake_case)] // the C++ names `V`, `ChainCheck`

use std::collections::HashMap;
use std::rc::Rc;

use fp_core::chain::public::{Binder, Public};
use fp_core::chain::rounds::VerifierRounds;
use fp_core::chain::session::VerifierSession;
use fp_core::code::code::Code;
use fp_core::field::ext::{E, F};
use fp_core::hash::calls::HashCalls;
use fp_core::hash::modes::Digest;
use fp_core::iop::context::{OracleNotice, VerifierContext};
use fp_core::iop::iopp::{IoppChoice, IoppStage};
use fp_core::iop::laid::{IndexWeights, LaidBlock, LaidMatrix};
use fp_core::iop::message::Reader;
use fp_core::iop::relation::{Codes, OracleShape, Part};
use fp_core::iop::req::{
    req_fault, ReqLink, ReqMessage, ReqShape, REQ_MOST_ROWS,
};
use fp_core::iop::req_rows::{
    req_layout_fault, ReqArray, ReqEquation, ReqLayout, ReqTerm,
};
use fp_core::numbers::codes::ceil_log2;
use fp_core::numbers::plan::{Cause, PlanRound, Planned, PricedCode, PricedGroup};
use fp_core::numbers::setting::{RoundKind, Setting};
use fp_core::verifier::request_chain::{chain_verify, ChainCheck, LinkHook};

const VECTORS: &str = include_str!("../../fixtures/req_chain_vectors.txt");

fn fields(line: &str) -> HashMap<&str, &str> {
    line.split_whitespace()
        .filter_map(|t| t.split_once('='))
        .map(|(k, v)| (k, v))
        .collect()
}

fn f(s: &str) -> F {
    F(u64::from_str_radix(s, 16).unwrap())
}

fn e3(a: &str, b: &str, c: &str) -> E {
    E([f(a), f(b), f(c)])
}

fn e_of(s: &str) -> E {
    let p: Vec<&str> = s.split(',').collect();
    assert_eq!(p.len(), 3, "an E value {}", s);
    e3(p[0], p[1], p[2])
}

/// `rows=e:<n>,lo,hi,...` or `rows=w:<n>,v,...`: the components of each E are comma separated.
fn weights(s: &str) -> IndexWeights {
    let (kind, rest) = s.split_once(':').expect("a weight vector");
    let mut parts = rest.split(',');
    let n: usize = parts.next().unwrap().parse().unwrap();
    if kind == "w" {
        let mut values = Vec::with_capacity(n);
        for _ in 0..n {
            values.push(e3(parts.next().unwrap(), parts.next().unwrap(), parts.next().unwrap()));
        }
        IndexWeights::written(Rc::new(values))
    } else {
        let mut w = IndexWeights::default();
        for _ in 0..n {
            let lo = e3(parts.next().unwrap(), parts.next().unwrap(), parts.next().unwrap());
            let hi = e3(parts.next().unwrap(), parts.next().unwrap(), parts.next().unwrap());
            w.lo.push(lo);
            w.hi.push(hi);
        }
        w
    }
}

/// `MASKS l=<l> n=<count>,<E>,<E>,...`
fn masks(line: &str) -> (usize, Vec<E>) {
    let kv = fields(line);
    let l: usize = kv["l"].parse().unwrap();
    let (_, rest) = line.split_once(" n=").expect("MASKS n=");
    let mut parts = rest.split(',');
    let n: usize = parts.next().unwrap().parse().unwrap();
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(e3(parts.next().unwrap(), parts.next().unwrap(), parts.next().unwrap()));
    }
    (l, out)
}

fn hex_bytes(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect()
}

fn kind(n: u32) -> RoundKind {
    match n {
        1 => RoundKind::Algebraic,
        2 => RoundKind::Epsilon,
        3 => RoundKind::Seed,
        4 => RoundKind::Positions,
        5 => RoundKind::Bits,
        6 => RoundKind::Seal,
        7 => RoundKind::Record,
        _ => RoundKind::Empty,
    }
}

#[derive(Clone, Debug, Default)]
struct Verdicts {
    honest_chain: bool,
    honest_calls: bool,
    spoil: bool,
    false_chain: bool,
    false_calls: bool,
    no_close: Vec<bool>,
    no_moment: Vec<bool>,
}

#[derive(Clone, Debug)]
struct Case {
    name: String,
    seed: u64,
    codes: Codes,
    shape: ReqShape,
    layout: ReqLayout,
    /// By link.
    terms: Vec<Vec<ReqTerm>>,
    masks: Vec<Vec<E>>,
    setting: Setting,
    rounds: Vec<PlanRound>,
    proof: Vec<u8>,
    false_proof: Vec<u8>,
    verdicts: Verdicts,
}

impl Case {
    fn new() -> Self {
        Case {
            name: String::new(),
            seed: 0,
            codes: Codes { base: Vec::new(), mask: Vec::new() },
            shape: ReqShape::default(),
            layout: ReqLayout::default(),
            terms: Vec::new(),
            masks: Vec::new(),
            setting: Setting::goldilocks(),
            rounds: Vec::new(),
            proof: Vec::new(),
            false_proof: Vec::new(),
            verdicts: Verdicts::default(),
        }
    }

    fn planned(&self) -> Planned {
        Planned {
            set: self.setting.clone(),
            rounds: self.rounds.clone(),
            messages: Vec::new(),
            parts: Vec::new(),
            cause: Cause::None,
            why_not: String::new(),
        }
    }

    fn equation(&self, l: usize) -> ReqEquation {
        ReqEquation {
            terms: self.terms[l].clone(),
            on_masks: self.masks[l].clone(),
            target: E::default(),
        }
    }
}

fn parse(text: &str) -> (Vec<Case>, Vec<(String, Option<String>)>) {
    let mut cases: Vec<Case> = Vec::new();
    let mut faults: Vec<(String, Option<String>)> = Vec::new();
    let mut cur = Case::new();
    for line in text.lines() {
        let tag = line.split_whitespace().next().unwrap_or("");
        let kv = fields(line);
        match tag {
            "CASE" => {
                cur = Case::new();
                cur.name = kv["name"].to_string();
                cur.seed = kv["seed"].parse().unwrap();
            }
            "CODE" => {
                let c = Code {
                    log_n: kv["log_n"].parse().unwrap(),
                    ell: kv["ell"].parse().unwrap(),
                    r: kv["r"].parse().unwrap(),
                };
                if line.split_whitespace().nth(1) == Some("base") {
                    cur.codes.base.push(c);
                } else {
                    cur.codes.mask.push(c);
                }
            }
            "SHAPE" => {
                cur.shape.code = kv["code"].parse().unwrap();
                cur.shape.mask_code = kv["mask_code"].parse().unwrap();
                cur.shape.answers = kv["answers"].parse().unwrap();
                cur.shape.choice = IoppChoice { masks_ride: kv["masks_ride"] == "1" };
            }
            "LINK" => {
                cur.shape.link.push(ReqLink {
                    name: kv["name"].to_string(),
                    messages: Vec::new(),
                    plain: kv["plain"].parse().unwrap(),
                });
            }
            "MSG" => {
                let l: usize = kv["l"].parse().unwrap();
                let shape = OracleShape {
                    name: kv["name"].to_string(),
                    code: kv["code"].parse().unwrap(),
                    main_rows: kv["main_rows"].parse().unwrap(),
                    main_deg: kv["main_deg"].parse().unwrap(),
                    mask_rows: kv["mask_rows"].parse().unwrap(),
                    mask_code: kv["mask_code"].parse().unwrap(),
                    answers: kv["answers"].parse().unwrap(),
                };
                cur.shape.link[l].messages.push(ReqMessage {
                    shape,
                    leaf_class: kv["leaf"].parse().unwrap(),
                    moment: kv["moment"].parse().unwrap(),
                    life: kv["life"].parse().unwrap(),
                });
            }
            "NOTICE" => {
                cur.shape.at_start.push(OracleNotice {
                    shape: OracleShape {
                        name: kv["name"].to_string(),
                        code: kv["code"].parse().unwrap(),
                        main_rows: kv["main_rows"].parse().unwrap(),
                        main_deg: kv["main_deg"].parse().unwrap(),
                        mask_rows: kv["mask_rows"].parse().unwrap(),
                        mask_code: kv["mask_code"].parse().unwrap(),
                        answers: kv["answers"].parse().unwrap(),
                    },
                    leaf_class: kv["leaf"].parse().unwrap(),
                });
            }
            "STAGE" => {
                cur.shape.last.push(IoppStage {
                    code: kv["code"].parse().unwrap(),
                    mask_code: kv["mask_code"].parse().unwrap(),
                    k: kv["k"].parse().unwrap(),
                    h: kv["h"].parse().unwrap(),
                });
            }
            "LAYOUT" => {
                let l: usize = kv["l"].parse().unwrap();
                if cur.layout.link.len() <= l {
                    cur.layout.link.resize_with(l + 1, Vec::new);
                }
                cur.layout.link[l].push(ReqArray {
                    name: kv["name"].to_string(),
                    message: kv["message"].parse().unwrap(),
                    laid: LaidMatrix {
                        size_i: kv["size_i"].parse().unwrap(),
                        size_c: kv["size_c"].parse().unwrap(),
                        blocks: Vec::new(),
                    },
                });
            }
            "BLOCK" => {
                let l: usize = kv["l"].parse().unwrap();
                let a: usize = kv["a"].parse().unwrap();
                cur.layout.link[l][a].laid.blocks.push(LaidBlock {
                    first_i: kv["fi"].parse().unwrap(),
                    bits_i: kv["bi"].parse().unwrap(),
                    first_c: kv["fc"].parse().unwrap(),
                    bits_c: kv["bc"].parse().unwrap(),
                    first_row: kv["fr"].parse().unwrap(),
                    row_bits: kv["rb"].parse().unwrap(),
                    first_place: kv["fp"].parse().unwrap(),
                    place_bits: kv["pb"].parse().unwrap(),
                    i_is_low: kv["low"] == "1",
                });
            }
            "TERM" => {
                let l: usize = kv["l"].parse().unwrap();
                if cur.terms.len() <= l {
                    cur.terms.resize_with(l + 1, Vec::new);
                }
                cur.terms[l].push(ReqTerm {
                    born: kv["born"].parse().unwrap(),
                    array: kv["array"].to_string(),
                    scale: e_of(kv["scale"]),
                    on_rows: weights(kv["rows"]),
                    on_columns: weights(kv["cols"]),
                });
            }
            "MASKS" => {
                let (l, v) = masks(line);
                if cur.masks.len() <= l {
                    cur.masks.resize_with(l + 1, Vec::new);
                }
                cur.masks[l] = v;
            }
            "SET" => {
                cur.setting.salt_bytes = kv["salt"].parse().unwrap();
                cur.setting.nonce_bytes = kv["nonce"].parse().unwrap();
                cur.setting.position_bytes = kv["position"].parse().unwrap();
                cur.setting.samples = kv["samples"].parse().unwrap();
                cur.setting.saved_coefficient = kv["saved"] == "1";
                cur.setting.target = kv["target"].parse().unwrap();
            }
            "ROUND" => {
                let mut r = PlanRound::default();
                // The name is last: it may hold spaces ("SEND seed").
                r.name = line.split_once(" name=").expect("a round's name").1.to_string();
                r.kind = kind(kv["kind"].parse().unwrap());
                r.work_bits = kv["work"].parse().unwrap();
                r.count = kv["count"].parse().unwrap();
                r.message_bytes = kv["msg"].parse().unwrap();
                r.roots = kv["roots"].parse().unwrap();
                r.answers = kv["answers"].parse().unwrap();
                r.draw_e = kv["draw_e"].parse().unwrap();
                r.draw_nonzero = kv["nz"].parse().unwrap();
                r.draw_positions = kv["draw_pos"].parse().unwrap();
                r.log_n = kv["log_n"].parse().unwrap();
                r.draw_trits = kv["trits"].parse().unwrap();
                r.rows = kv["rows"].parse().unwrap();
                r.first_list = kv["first_list"].parse().unwrap();
                r.combinations = kv["combos"].parse().unwrap();
                r.sharing = kv["sharing"].parse().unwrap();
                r.group = PricedGroup {
                    main: PricedCode {
                        log_n: kv["gml"].parse().unwrap(),
                        ell: kv["gme"].parse().unwrap(),
                        r: kv["gmr"].parse().unwrap(),
                    },
                    mask: PricedCode {
                        log_n: kv["gzl"].parse().unwrap(),
                        ell: kv["gze"].parse().unwrap(),
                        r: kv["gzr"].parse().unwrap(),
                    },
                    k: kv["gk"].parse().unwrap(),
                    h: kv["gh"].parse().unwrap(),
                    slots: kv["gslots"].parse().unwrap(),
                    said: kv["gsaid"] == "1",
                    rule: 0,
                    m: 0,
                };
                cur.rounds.push(r);
            }
            "PROOF_HEX" => cur.proof = hex_bytes(line.split_whitespace().nth(1).unwrap()),
            "FALSEPROOF_HEX" => {
                cur.false_proof = hex_bytes(line.split_whitespace().nth(1).unwrap())
            }
            "VERDICT" => {
                cur.verdicts.honest_chain = kv["honest_chain"] == "1";
                cur.verdicts.honest_calls = kv["honest_calls"] == "1";
                cur.verdicts.spoil = kv["spoil"] == "1";
                cur.verdicts.false_chain = kv["false_chain"] == "1";
                cur.verdicts.false_calls = kv["false_calls"] == "1";
            }
            "NOCLOSE" => {
                let l: usize = kv["l"].parse().unwrap();
                if cur.verdicts.no_close.len() <= l {
                    cur.verdicts.no_close.resize(l + 1, false);
                }
                cur.verdicts.no_close[l] = kv["ok"] == "1";
            }
            "NOMOMENT" => {
                let l: usize = kv["l"].parse().unwrap();
                if cur.verdicts.no_moment.len() <= l {
                    cur.verdicts.no_moment.resize(l + 1, false);
                }
                cur.verdicts.no_moment[l] = kv["ok"] == "1";
            }
            "ENDCASE" => cases.push(core::mem::replace(&mut cur, Case::new())),
            "FAULT" => {
                let key = kv["key"].to_string();
                let name = line.split_once("name=").map(|(_, n)| n.to_string());
                let name = match name {
                    Some(n) if n != "-" => Some(n),
                    _ => None,
                };
                faults.push((key, name));
            }
            _ => {}
        }
    }
    (cases, faults)
}

fn toy_configuration() -> Digest {
    let mut d = Digest::zero();
    d.w[0] = 0x00796f74;
    d
}

struct Run<'a> {
    binder: Binder,
    codes: Public<Codes>,
    reader: Reader<'a>,
    session: VerifierSession,
    calls: HashCalls,
}

fn run_setup<'a>(case: &Case, proof: &'a [u8]) -> Run<'a> {
    let mut binder = Binder::new(1, Rc::new(case.planned()));
    binder.configuration(&toy_configuration());
    let codes = binder.parameter("codes", case.codes.clone());
    let _shape = binder.parameter("request", case.shape.clone());
    let _layout = binder.parameter("layout", case.layout.clone());
    let _seed = binder.statement("seed of the weights", case.seed);
    Run {
        binder,
        codes,
        reader: Reader::new(proof),
        session: VerifierSession::new(),
        calls: HashCalls::new(),
    }
}

struct MadeUpHook<'a> {
    case: &'a Case,
    link: usize,
    spoil: bool,
    target: E,
}

impl LinkHook for MadeUpHook<'_> {
    fn run(
        &mut self,
        moment: u32,
        V: &mut VerifierContext<'_, '_, '_, '_>,
        frame: &fp_core::iop::req::ReqFrame,
        _sent: &[u32],
        _calls: &mut HashCalls,
    ) -> bool {
        if moment + 1 < frame.shape().link[self.link].moments() {
            return true;
        }
        V.ch.recv_e(&mut self.target)
    }
    fn claim(&mut self, target: &mut E, on_masks: &mut Vec<E>) {
        *target = self.target;
        *on_masks = self.case.masks[self.link].clone();
    }
    fn terms(&mut self) -> Vec<ReqTerm> {
        let mut terms = self.case.terms[self.link].clone();
        if self.spoil {
            terms[0].scale = terms[0].scale + E::one();
        }
        terms
    }
}

fn verify_chain(case: &Case, proof: &[u8], spoil: bool) -> bool {
    let mut r = run_setup(case, proof);
    let mut ch =
        VerifierRounds::new(&mut r.binder, &mut r.reader, &mut r.session, &mut r.calls);
    let ok;
    {
        let mut made: Vec<MadeUpHook> = (0..case.shape.link.len())
            .map(|l| MadeUpHook { case, link: l, spoil: spoil && l == 0, target: E::default() })
            .collect();
        let mut hooks: Vec<&mut dyn LinkHook> =
            made.iter_mut().map(|h| h as &mut dyn LinkHook).collect();
        let mut v = VerifierContext::new(&r.codes, &mut ch);
        ok = chain_verify(&mut v, case.shape.clone(), &case.layout, &mut hooks, &mut r.calls);
    }
    ok && ch.finish()
}

fn verify_by_calls(
    case: &Case,
    proof: &[u8],
    no_close: Option<usize>,
    no_moment: Option<usize>,
) -> bool {
    let mut r = run_setup(case, proof);
    let mut ch =
        VerifierRounds::new(&mut r.binder, &mut r.reader, &mut r.session, &mut r.calls);
    let mut ok = true;
    {
        let mut v = VerifierContext::new(&r.codes, &mut ch);
        {
            let mut check = ChainCheck::new(&mut v, case.shape.clone(), case.layout.clone());
            'links: for l in 0..case.shape.link.len() {
                if !check.first(&mut r.calls) {
                    ok = false;
                    break;
                }
                let moments = case.shape.link[l].moments();
                let upto = if no_moment == Some(l) { moments - 1 } else { moments };
                for _ in 1..upto {
                    if !check.later(&mut r.calls) {
                        ok = false;
                        break 'links;
                    }
                }
                if no_close == Some(l) {
                    continue;
                }
                let mut eq = case.equation(l);
                if !check.ctx().ch.recv_e(&mut eq.target) {
                    ok = false;
                    break;
                }
                if !check.close(&eq, &mut r.calls) {
                    ok = false;
                    break;
                }
            }
            if ok && !check.finish(&mut r.calls) {
                ok = false;
            }
        }
    }
    ok && ch.finish()
}

#[test]
fn the_cpp_request_chain_proofs_are_accepted_and_the_hostile_runs_rejected() {
    let (cases, faults) = parse(VECTORS);
    assert_eq!(cases.len(), 4, "four toy cases");
    for case in &cases {
        assert_eq!(
            verify_chain(case, &case.proof, false),
            case.verdicts.honest_chain,
            "{}: chain_verify on the honest proof",
            case.name
        );
        assert_eq!(
            verify_by_calls(case, &case.proof, None, None),
            case.verdicts.honest_calls,
            "{}: ChainCheck's calls on the honest proof",
            case.name
        );
        assert_eq!(
            verify_chain(case, &case.proof, true),
            case.verdicts.spoil,
            "{}: another weight is rejected",
            case.name
        );
        assert_eq!(
            verify_chain(case, &case.false_proof, false),
            case.verdicts.false_chain,
            "{}: a false target is rejected by chain_verify",
            case.name
        );
        assert_eq!(
            verify_by_calls(case, &case.false_proof, None, None),
            case.verdicts.false_calls,
            "{}: a false target is rejected by the calls",
            case.name
        );
        for l in 0..case.shape.link.len() {
            assert_eq!(
                verify_by_calls(case, &case.proof, Some(l), None),
                case.verdicts.no_close[l],
                "{}: a link without its close",
                case.name
            );
            assert_eq!(
                verify_by_calls(case, &case.proof, None, Some(l)),
                case.verdicts.no_moment[l],
                "{}: a link without its last moment",
                case.name
            );
        }
    }

    // The fault battery: each mutation of the first case's shape or layout, and the name that the
    // C++ check returned for it. The Rust check returns the same names, item by item.
    let case = &cases[0];
    let got = fault_battery(case);
    assert_eq!(got.len(), faults.len(), "the battery's length");
    for ((key, want), (got_key, got)) in faults.iter().zip(got.iter()) {
        assert_eq!(key, got_key, "the battery's order");
        assert_eq!(got.as_deref(), want.as_deref(), "the fault name for {}", key);
    }
}

// ---------------------------------------------------------------------------------------------------------------------
// The fault battery: the mutations of req_chain_vectors.cpp, by key.
// ---------------------------------------------------------------------------------------------------------------------

fn with_shape(case: &Case, change: impl FnOnce(&mut ReqShape)) -> Option<&'static str> {
    let mut shape = case.shape.clone();
    change(&mut shape);
    req_fault(&case.codes, &shape)
}

fn with_layout(
    case: &Case,
    change: impl FnOnce(&mut ReqShape, &mut ReqLayout),
) -> Option<&'static str> {
    let mut shape = case.shape.clone();
    let mut layout = case.layout.clone();
    change(&mut shape, &mut layout);
    req_layout_fault(&case.codes, &shape, &layout)
}

fn fault_battery(case: &Case) -> Vec<(String, Option<&'static str>)> {
    let mut out: Vec<(String, Option<&'static str>)> = Vec::new();
    let links = case.shape.link.len();

    out.push((
        String::from("answers_zero"),
        with_shape(case, |s| s.answers = 0),
    ));
    out.push((
        String::from("message_no_rows"),
        with_shape(case, |s| {
            s.link[0].messages[0].shape.main_rows = 0;
            s.link[0].messages[0].shape.mask_rows = 0;
        }),
    ));
    out.push((
        String::from("message_too_many_rows"),
        with_shape(case, |s| s.link[0].messages[0].shape.main_rows = REQ_MOST_ROWS + 1),
    ));
    out.push((
        String::from("message_bad_degree"),
        with_shape(case, |s| s.link[0].messages[0].shape.main_deg = 2),
    ));
    out.push((
        String::from("kept_with_mask"),
        with_shape(case, |s| s.link[0].messages[0].life = 1),
    ));
    out.push((
        String::from("moment_gap"),
        with_shape(case, |s| {
            let mut m = s.link[0].messages[1].clone();
            m.moment = 9;
            s.link[0].messages.push(m);
        }),
    ));
    out.push((
        String::from("answers_mismatch"),
        with_shape(case, |s| s.link[0].messages[1].shape.answers = 2),
    ));
    out.push((
        String::from("main_code_mismatch"),
        with_shape(case, |s| s.link[0].messages[0].shape.code = 1),
    ));
    out.push((
        String::from("mask_code_mismatch"),
        with_shape(case, |s| s.link[0].messages[0].shape.mask_code = 1),
    ));
    out.push((
        String::from("kept_beyond_last"),
        with_shape(case, |s| {
            s.link[0].messages[0].shape.mask_rows = 0;
            s.link[0].messages[0].life = links as u32;
        }),
    ));
    out.push((
        String::from("first_link_no_fold"),
        with_shape(case, |s| {
            s.link[0].messages.retain(|m| m.moment == 0);
            for m in &mut s.link[0].messages {
                m.shape.mask_rows = 0;
                m.life = 1;
            }
        }),
    ));
    out.push((
        String::from("at_start_main_rows"),
        with_shape(case, |s| {
            s.at_start.push(OracleNotice {
                shape: OracleShape {
                    name: String::from("rider"),
                    main_rows: 1,
                    mask_rows: 1,
                    mask_code: 0,
                    answers: s.answers,
                    ..OracleShape::default()
                },
                leaf_class: 1,
            });
        }),
    ));
    out.push((
        String::from("at_start_answers"),
        with_shape(case, |s| {
            s.at_start.push(OracleNotice {
                shape: OracleShape {
                    name: String::from("rider"),
                    mask_rows: 1,
                    mask_code: 0,
                    answers: 99,
                    ..OracleShape::default()
                },
                leaf_class: 1,
            });
        }),
    ));
    out.push((
        String::from("at_start_class"),
        with_shape(case, |s| {
            s.at_start.push(OracleNotice {
                shape: OracleShape {
                    name: String::from("rider"),
                    mask_rows: 1,
                    mask_code: 0,
                    answers: s.answers,
                    ..OracleShape::default()
                },
                leaf_class: 0,
            });
        }),
    ));
    out.push((
        String::from("last_too_few"),
        with_shape(case, |s| s.last.truncate(1)),
    ));
    out.push((
        String::from("last_group"),
        with_shape(case, |s| s.last[0].k += 1),
    ));
    out.push((
        String::from("code_missing"),
        with_shape(case, |s| {
            let bad = case.codes.base.len() as u32;
            s.code = bad;
            for l in &mut s.link {
                for m in &mut l.messages {
                    if m.shape.main_rows > 0 {
                        m.shape.code = bad;
                    }
                }
            }
            s.last[0].code = bad;
        }),
    ));
    out.push((
        String::from("answers_too_many"),
        with_shape(case, |s| {
            let many = case.codes.base[0].ell as u32;
            s.answers = many;
            for l in &mut s.link {
                for m in &mut l.messages {
                    m.shape.answers = many;
                }
            }
        }),
    ));

    out.push((
        String::from("layout_link_count"),
        with_layout(case, |_, lay| {
            lay.link.pop();
        }),
    ));
    out.push((
        String::from("layout_message_missing"),
        with_layout(case, |_, lay| lay.link[0][0].message = 99),
    ));
    out.push((
        String::from("layout_duplicate_name"),
        with_layout(case, |_, lay| {
            let first = lay.link[0][0].name.clone();
            lay.link[0][1].name = first;
        }),
    ));
    out.push((
        String::from("layout_bad_block"),
        with_layout(case, |_, lay| lay.link[0][0].laid.blocks[0].first_i = 1),
    ));
    out.push((
        String::from("layout_row_unsent"),
        with_layout(case, |_, lay| {
            lay.link[0].push(ReqArray {
                name: String::from("U"),
                message: 0,
                laid: LaidMatrix {
                    size_i: 1,
                    size_c: 1,
                    blocks: vec![LaidBlock { first_row: 3, ..LaidBlock::default() }],
                },
            });
        }),
    ));
    out.push((
        String::from("layout_pad"),
        with_layout(case, |s, lay| {
            let mut m = 0usize;
            while m + 1 < s.link[0].messages.len() && s.link[0].messages[m].shape.mask_rows > 0 {
                m += 1;
            }
            let o = s.link[0].messages[m].shape.clone();
            let row_bits = ceil_log2(o.main_rows as u64);
            let pad = fp_core::iop::send_pad::send_pad(&case.codes, &o)
                .into_iter()
                .find(|p| p.part == Part::Main)
                .expect("a main-row pad");
            let b = LaidBlock {
                first_row: pad.index & ((1u64 << row_bits) - 1),
                first_place: pad.index >> row_bits,
                ..LaidBlock::default()
            };
            lay.link[0].push(ReqArray {
                name: String::from("P"),
                message: m,
                laid: LaidMatrix { size_i: 1, size_c: 1, blocks: vec![b] },
            });
        }),
    ));

    out
}
