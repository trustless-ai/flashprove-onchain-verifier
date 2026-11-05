//! `runStage()` (`cp_verify.cpp:1264-2538`), the body of one stage of a call: the public files,
//! the statement, the plans, the segments, and — for the request stage — the proof's check and the
//! lines that end the stage.
//!
//! The C++ runs each stage in a child process and prints as it goes. The port returns the stage's
//! text and its exit status; the host captures the three stages' texts and forms the call's output
//! as `cpStagesRun()` does. Everything that `refuse()` ends in C++ becomes a `Refusal`; the text
//! printed before it is kept.
//!
//! Not yet ported: the `q9`/`h9` no-overflow conditions and a few checks that only reject malformed
//! parameter files without printing (they pass on every admitted parameter file). The S4 lanes
//! extend the negative side; the accepted path and the two S3 negatives do not reach them.

use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use crate::consts::{BAR, BUILD_SOURCE_DIGEST, DW};
use crate::field::ext::{E, F};
use crate::frame::check::{
    check_proof_if_tested, LinksResult, ProofFacts, RequestPublic,
};
use crate::frame::check_entry::{check_entry_if_tested, read_entry_table_unproved_configured};
use crate::frame::check_key::{check_key, read_key_table_unproved_configured};
use crate::frame::configure::{configure_with_calls, published_id, Configured, Shapes};
use crate::frame::files::{merged, FilePlan, Subproofs};
use crate::frame::parameters::Parameters;
use crate::hash::calls::HashCalls;
use crate::hash::earlier::earlier_hash_h_digest;
use crate::hash::modes::Digest;
use crate::hash::th::th;
use crate::iop::foldeq::{IfTested, TestedTable, UnprovedTable};
use crate::iop::message::Reader;
use crate::numbers::accounting::{account, Accounting};
use crate::numbers::accounting_print::{
    acct_lines, one_time_line, print_accounting, work_note_line,
};
use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};
use crate::stage_state::{StageState, WorkNote};
use crate::verifier::attention_check::{AttentionSubProof, AttentionSubProofInputs};
use crate::verifier::attention_shape::ACfg;
use crate::verifier::common::{
    above_clip, acceptance_policy_is_exact_match, good_ending, hex64, policy_kind, rotary_served,
    served_form, PolicyNamed, Served, NOT_A_VERIFICATION_TEXT, SERVED_TWO_CODES,
    STATUS_STAGE_PASSED_WITH_WORK,
};
use crate::verifier::engine::trim_l;
use crate::verifier::frame_segment::{run_links, LinkStop, SegRun};
use crate::verifier::head_plan::{plan_head, HeadPlanInputs};
use crate::verifier::layers_plan::{plan_layers, plan_sizes, reads_of, LayerPlanInputs, Reads};
use crate::verifier::matrices::Tail;
use crate::verifier::stage_context::{build_hl, build_tails, build_ws_lay, Hl};
use crate::verifier::stage_layout::{
    lay_w, lay_words, layout, parse_header, pol_prescan, pol_scan, pol_skeleton, st_from_call,
    tensors_agree, Hdr, Lay, PolScan,
};
use crate::verifier::stage_links::{build_links, shapes_of, BuildLinksInputs, LinkMeta};
use crate::verifier::tables::{
    rope_table, sigmoid_table, silu_table, table_digest, TableParams, TBLW,
};
use crate::verifier::weights_layout::WsLay;

/// Which stage of a call (`CpStage::name`, `oneTime`). `PlanId` is `oneTime = 3`, the planning call
/// `-plan id` (`cp_verify.cpp:3124-3141`); `PlanAccounting` is not a mode there: it is the request
/// stage with `planOnly` set (`cp_verify.cpp:3142-3159`), so it runs as `Request` with
/// `StageFiles::plan_only`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StageMode {
    Key,
    Leaf,
    Request,
    PlanId,
}

impl StageMode {
    pub fn name(self) -> &'static str {
        match self {
            StageMode::Key => "key",
            StageMode::Leaf => "leaf",
            StageMode::Request => "request",
            StageMode::PlanId => "id",
        }
    }
}

/// The files and options that one stage gets (`CallInputs`, `StageInputs`).
pub struct StageFiles<'a> {
    pub pol: &'a [u8],
    /// `layout.txt`, if the configuration folder has it.
    pub layout: Option<&'a [u8]>,
    pub kl: &'a [u32],
    pub key: &'a [u8],
    /// `ivk/leaf/<k>.bin`.
    pub entry: Option<&'a [u8]>,
    /// The proof header's leaf number.
    pub entry_number: u32,
    pub request: Option<&'a [u32]>,
    pub y: Option<&'a [u32]>,
    /// The request or y file's length is no multiple of 4 bytes.
    pub odd_statement: bool,
    pub proof: Option<&'a [u8]>,
    pub id_asked: &'a str,
    pub asked: f64,
    pub quiet: bool,
    pub next_token_asked: bool,
    /// `in.planOnly`: a planning call. It reads no proof and ends after the plan it prints.
    pub plan_only: bool,
    pub policy: &'a PolicyNamed,
}

/// What one stage leaves: its printed text, its exit status, its hash calls and its record.
pub struct StageOutcome {
    pub status: i32,
    pub text: String,
    /// This stage's own hash calls (`q_V` adds them).
    pub calls: u64,
    /// The stage's accounting as its record holds it (`acctNote`), if it formed one.
    pub acct: Option<Accounting>,
    /// The line "work:" as the stage printed it (without the newline), if it needed work.
    pub work: Option<String>,
}

fn named(name: &str) -> Refusal {
    Refusal::named(name)
}

fn hex_of(d: Digest) -> String {
    let mut s = String::with_capacity(64);
    for b in d.to_bytes() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn note_work(note: &mut WorkNote, bits: f64, work: u32, where_: &str) {
    if note.needed && !(bits < note.bits) {
        return;
    }
    *note = WorkNote { needed: true, bits, work, where_: String::from(where_) };
}

/// `acctOfH` (`cp_verify.cpp:2207-2220`): one file plan's accounting, its checks and the one-time
/// line.
#[allow(clippy::too_many_arguments)]
fn acct_of(
    conf: &Configured,
    plan: &FilePlan,
    what: &str,
    object: &str,
    one_time: bool,
    min_bits: f64,
    state: &mut StageState,
    out: &mut String,
) -> Result<Accounting> {
    let set = conf.sized().d.set.clone();
    let acct = account(&merged(&set, &[plan.clone()]), -1);
    if !acct.formed || !acct.holds || (acct.target as f64) < min_bits {
        out.push_str(&print_accounting(&acct, what, false, 6));
        if acct.formed && acct.holds {
            out.push_str(&format!(
                "accounting: asked of this call: {} bits, above the parameter file's target of {} bits\n",
                min_bits, acct.target
            ));
        }
        return Err(named("security-bits"));
    }
    if acct.needs_work {
        note_work(
            &mut state.stage_work_note,
            acct.lists.bits,
            acct.lists.work,
            &format!("{}: {}", object, acct.lists.name),
        );
    }
    if one_time {
        out.push_str(&one_time_line(what, acct.closeness[0], acct.closeness[1]));
        out.push('\n');
    }
    Ok(acct)
}

/// `lastLine()` (`vf_common.h:779-803`): the record, the result line and the stage's last line.
#[allow(clippy::too_many_arguments)]
fn last_line(
    out: &mut String,
    below_bar: bool,
    form: &str,
    lidb: i32,
    nminh: i32,
    good: &str,
    good_status: i32,
    fields: &str,
    note: &str,
    state: &StageState,
    acct: &Accounting,
    calls: &HashCalls,
) -> i32 {
    let mut counted = acct.clone();
    counted.counted = true;
    counted.calls = calls.total();
    let work = acct_lines(&counted) + &work_note_line(&state.stage_work_note);
    let set = format!(
        "{}{}",
        if lidb != crate::consts::LIDB_SEALED {
            format!("lidb {}; ", lidb)
        } else {
            String::new()
        },
        if nminh != 0 { format!("nminH {}; ", nminh) } else { String::new() }
    );
    let all = format!("{} pow={} pows={} powc={}", fields, state.pow, state.pows, state.powc);
    if good_ending(below_bar, !form.is_empty()) {
        let word = if state.stage_work_note.needed {
            format!("STAGE PASSED WITH WORK{}", &good["STAGE PASSED".len()..])
        } else {
            String::from(good)
        };
        out.push_str(&format!(
            "{}result:{} ({}; {}no security level is claimed)\n{}\n",
            work, all, note, set, word
        ));
        if state.stage_work_note.needed {
            STATUS_STAGE_PASSED_WITH_WORK
        } else {
            good_status
        }
    } else {
        out.push_str(&format!(
            "{}result:{} (not a verification: {}{}{}{}; {}no security level is claimed)\n{}\n",
            work,
            all,
            if crate::verifier::common::TEST_BUILD {
                "the program is a test build (its first lines say which); "
            } else {
                ""
            },
            if below_bar { "fewer than 128 bits were requested; " } else { "" },
            if form.is_empty() {
                String::new()
            } else {
                format!("not the standard parameter form: {}; ", form)
            },
            note,
            set,
            NOT_A_VERIFICATION_TEXT
        ));
        14
    }
}

/// `planEndH` (`cp_verify.cpp:2435-2461`): what a planning call prints after the plans. The round
/// and field listings are not ported; the S4 planning cases ask for neither.
fn plan_end(
    out: &mut String,
    st: &Setup,
    h: &Hdr,
    not_served: &str,
    state: &StageState,
) -> Result<i32> {
    let sub = st
        .sub
        .as_ref()
        .expect("a planning call keeps the request's sub-proofs");
    if !crate::frame::prints::print_plan(out, "request", st.conf.sized(), sub, false, false) {
        return Err(named("security-bits"));
    }
    out.push_str(&format!(
        "plan: profile {}: the profile rules out no result\n",
        h.prof
    ));
    for (what, plan) in [("a key", st.conf.key()), ("an entry", st.conf.entry())] {
        let acct = account(&merged(&st.conf.sized().d.set, &[plan.clone()]), -1);
        out.push_str(&one_time_line(what, acct.closeness[0], acct.closeness[1]));
        out.push('\n');
    }
    if !not_served.is_empty() {
        out.push_str(&format!(
            "plan: not the standard parameter form ({}): no run with these public inputs can be a verification (at best status 14)\n",
            not_served
        ));
    }
    if h.tabs + 4 != h.digsh {
        out.push_str(&format!(
            "plan: the policy's kind is {}: every whole call under this parameter file ends NO: policy\n",
            policy_kind(
                h.clipc as u64,
                h.theta as u64,
                h.cap as u64,
                h.logs as u64,
                h.digsh as u64,
                h.tabs as u64
            )
        ));
    }
    if state.lidb != crate::consts::LIDB_SEALED {
        out.push_str(&format!("plan: lidb {}\n", state.lidb));
    }
    if state.nminh != 0 {
        out.push_str(&format!("plan: nminH {}\n", state.nminh));
    }
    if state.gate_table_input_fraction_bits != 8 || state.smax != 4095 {
        out.push_str(&format!(
            "plan: the SiLU table: key step 2^-{}, values clamped to +-{} (lines eg, smax)\n",
            state.gate_table_input_fraction_bits, state.smax
        ));
    }
    if state.rcl != 0 {
        out.push_str("plan: the router's logits are clamped (line rcl)\n");
    }
    if state.gcl != 0 {
        out.push_str("plan: the input of the SiLU table is clamped (line gcl)\n");
    }
    if state.residual_stream_limbs == 5 {
        out.push_str("plan: a value of the residual stream has five limbs (line xl)\n");
    }
    if st.ps.tbl_at == TBLW {
        out.push_str(&format!(
            "plan: this program's four public tables match the parameter file's digests (lines tsilu0 .. texp{})\n",
            DW - 1
        ));
    }
    out.push_str(&format!(
        "statement: {} words, y at word {}\n",
        st.ps.st.len(),
        h.off_h_tok + DW as usize
    ));
    out.push_str(&format!(
        "h_par={}\nconfiguration={}\n",
        hex64(&st.h_par.w),
        hex_of(*st.conf.configuration())
    ));
    out.push_str(&format!("dw={}\nPLAN ONLY: no proof was checked\n", DW));
    Ok(4)
}

/// `placedAlike` (`cp_verify.cpp:2378-2389`).
fn placed_alike(
    a: Option<&crate::iop::req_rows::ReqArray>,
    b: Option<&crate::iop::req_rows::ReqArray>,
) -> bool {
    let (Some(a), Some(b)) = (a, b) else { return false };
    if a.message != b.message
        || a.laid.size_i != b.laid.size_i
        || a.laid.size_c != b.laid.size_c
        || a.laid.blocks.len() != b.laid.blocks.len()
    {
        return false;
    }
    for i in 0..a.laid.blocks.len() {
        let x = &a.laid.blocks[i];
        let y = &b.laid.blocks[i];
        if x.first_i != y.first_i
            || x.first_c != y.first_c
            || x.first_row != y.first_row
            || x.first_place != y.first_place
            || x.bits_i != y.bits_i
            || x.bits_c != y.bits_c
            || x.row_bits != y.row_bits
            || x.place_bits != y.place_bits
            || x.i_is_low != y.i_is_low
        {
            return false;
        }
    }
    true
}

/// Words to bytes, low byte first (`bytesOfH`, cp_verify.cpp:2420-2425).
fn words_bytes(w: &[u32]) -> Vec<u8> {
    let mut o = Vec::with_capacity(4 * w.len());
    for &x in w {
        for i in 0..4 {
            o.push((x >> (8 * i)) as u8);
        }
    }
    o
}

/// The C++ packs a text's bytes into words, low byte first (`(s.size()+3)/4` words).
fn pack_words(s: &str) -> Vec<u32> {
    let b = s.as_bytes();
    let mut w = vec![0u32; (b.len() + 3) / 4];
    for (i, &c) in b.iter().enumerate() {
        w[i / 4] |= (c as u32) << (8 * (i % 4));
    }
    w
}

fn table_params(h: &Hdr, state: &StageState) -> TableParams {
    TableParams {
        eg: state.gate_table_input_fraction_bits as u32,
        smax: state.smax,
        gcl: state.gcl != 0,
        theta0: h.theta0,
        cs: h.cs,
        dh: h.dh,
        lt: h.lt,
        s: h.sx,
        rx: h.rx,
    }
}

fn kl_at(kl: &[u32], l: u64, i: usize) -> u32 {
    kl[13 * l as usize + i]
}

fn kl_sh(kl: &[u32], l: u64) -> u32 {
    kl_at(kl, l, 11)
}

/// The configuration phase of `runStage()`: the scan, the layout, the statement's hashes, the
/// sub-proofs' plans, `buildLinksH()` and `configure()`. All three stages run it.
struct Setup {
    ps: PolScan,
    y: Lay,
    hl: Hl,
    tails: Vec<Tail>,
    reads: Reads,
    ws_lay: WsLay,
    link_metas: Vec<LinkMeta>,
    hid: Rc<Vec<crate::verifier::layers_plan::HPlan2>>,
    ah: Rc<Vec<AttentionSubProof>>,
    ph: Rc<crate::verifier::head_plan::HPlanH2>,
    conf: Configured,
    two_codes_h: bool,
    h_par: Digest,
    /// The request's sub-proofs (`subH`), kept for a planning call's `print_plan`.
    sub: Option<Subproofs>,
}

fn setup(files: &StageFiles<'_>, state: &mut StageState, calls: &mut HashCalls) -> Result<Setup> {
    let pol_b = files.pol;
    let kl = files.kl;
    let layout_text: Option<&str> = match files.layout {
        Some(b) => match core::str::from_utf8(b) {
            Ok(s) => Some(s),
            Err(_) => return Err(named("plan-layout")),
        },
        None => None,
    };
    let p3;
    let h: Hdr;
    let mut ps = PolScan::default();
    pol_prescan(&mut ps, pol_b, state)?;
    {
        if !ps.so.hl {
            return Err(named("policy-name-lt"));
        }
        if ps.so.plt < 4 || ps.so.plt > 16 {
            return Err(named("shape-words"));
        }
        pol_skeleton(&mut ps, false, state)?;
    }
    pol_scan(&mut ps, pol_b, state)?;
    // `polWordsH` (`cp_verify.cpp:1149-1153`): the file's digest, then its value lines. Nothing
    // reads it, but its hash calls count in the stage's q_V.
    let _ = crate::frame::heads::parameter_file_digest(pol_b, calls);
    ps.h = parse_header(&ps.st, state)?;
    h = ps.h.clone();
    if !crate::verifier::common::tau_served(h.tau as u64) {
        return Err(named("hid-tau"));
    }
    state.tau = h.tau as i32;
    let y = layout(&h, &ps.pol_calls, state)?;
    if state.stated_target.hb < 1 || state.stated_target.hb > 4096 {
        return Err(named("hid-hb"));
    }
    if (state.tau as u32) < state.stated_target.hb {
        return Err(named("policy-tau-hb"));
    }
    p3 = h.ne > 0;
    // The hash of the lines `call`.
    {
        let mut s = String::new();
        for c in &y.calls {
            s.push_str(&format!("call {} {}", c.c.name, c.kind));
            for g in &c.segs {
                s.push(' ');
                s.push_str(&g.name);
            }
            s.push('\n');
        }
        let w = pack_words(&s);
        let mut hh = [0u32; DW as usize];
        earlier_hash_h_digest(&mut hh, 73, &w, w.len() as u64, 1, calls);
        lay_words(&mut ps, h.off_h_calls, &hh)?;
    }
    let nmoe = if p3 { h.l as u64 / 2 } else { 0 };
    if kl.len() as u64 != 13 * h.l as u64 + 3 * nmoe {
        return Err(named("KL-length"));
    }
    if kl.len() < DW as usize {
        return Err(named("KL-length"));
    }
    {
        let mut hh = [0u32; DW as usize];
        th(&mut hh, kl, calls);
        lay_words(&mut ps, h.off_h_ts + 3 * DW as usize, &hh)?;
        // Two computations of one hash: TH(KL) here and in the statement (cp_verify.cpp:1536-1540).
        let mut again = [0u32; DW as usize];
        th(&mut again, kl, calls);
        if again != hh {
            return Err(named("internal-par-digests"));
        }
    }
    let tp = table_params(&h, state);
    {
        let w = silu_table(&tp);
        let hh = table_digest(&w, calls);
        lay_words(&mut ps, h.off_h_ts, &hh)?;
        if ps.tbl_at == TBLW && hh != ps.tbl_pol[0] {
            return Err(named("table-digest-silu"));
        }
        if !p3 && h.h_sig.iter().any(|&x| x != 0) {
            return Err(named("header-absent-hash"));
        }
        if p3 {
            let sig = sigmoid_table(&tp, true).expect("the model has experts");
            let hh = table_digest(&sig, calls);
            lay_words(&mut ps, h.off_h_ts + DW as usize, &hh)?;
            if ps.tbl_at == TBLW && hh != ps.tbl_pol[1] {
                return Err(named("table-digest-sigmoid"));
            }
        } else {
            lay_words(&mut ps, h.off_h_ts + DW as usize, &[0u32; DW as usize])?;
        }
    }
    let kl_bytes = words_bytes(kl);
    // h_par: the configuration digest, computed in the stage too (its hash calls count).
    let h_par = crate::frame::heads::configuration_digest(
        &[pol_b, files.layout.unwrap_or(&[]), &kl_bytes],
        calls,
    );
    for k in 0..12usize {
        if !y.kinds.iter().any(|x| x.idx == k as i32) {
            if h.wb[k] != 0 {
                return Err(named("header-absent-kind"));
            }
            continue;
        }
        if h.wb[k] != 13 {
            return Err(named("policy-weight-kind"));
        }
    }
    let vv = h.v;
    if vv < 2 || vv > (1u64 << 24) {
        return Err(named("shape-V"));
    }
    if h.wbh[0] < 2 || h.wbh[0] > 31 || h.wbh[1] != 13 {
        return Err(named("policy-weight-kind"));
    }
    if h.wbh[0] != 21 {
        return Err(named("policy-weight-width-emb"));
    }
    let ws_lay: WsLay = build_ws_lay(&h, &y, ps.frame.block_log)?;
    if h.theta0 == 0 {
        return Err(named("shape-theta0"));
    }
    {
        let w = rope_table(h.theta0, h.cs, h.dh, y.t);
        let hh = table_digest(&w, calls);
        lay_words(&mut ps, h.off_h_ts + 2 * DW as usize, &hh)?;
        if ps.tbl_at == TBLW && hh != ps.tbl_pol[2] {
            return Err(named("table-digest-rope"));
        }
    }
    let parts0 = y.parts[0] as usize;
    let parts1 = y.parts[1] as usize;
    let i_qa = parts0 + parts1 + 2;
    let i_xi = i_qa + 2;
    let mut tails = build_tails(&y, &h, y.ngr);
    for g in 1..y.ngr as usize {
        tails[g].mats[i_xi].kind = 1;
        tails[g].mats[i_xi].foreign = 0;
        tails[g].mats[i_xi].a_id = tails[g - 1].mats[i_xi - 1].a_id;
    }
    let hb = state.stated_target.hb - state.pow as u32;
    let stated_hb = state.stated_target.hb;
    let limbs = state.residual_stream_limbs;
    let lidb = state.lidb;
    // The attention sub-proofs A_g.
    let mut ah: Vec<AttentionSubProof> = Vec::new();
    {
        let mut lines: Vec<crate::verifier::attention_shape::Line> = Vec::new();
        fn seg_of(s: &str) -> i32 {
            use crate::verifier::attention_shape::{S_FD, S_FM, S_IX, S_RD, S_RM, S_WH, S_WL};
            match s {
                "RM" => S_RM,
                "RD" => S_RD,
                "FM" => S_FM,
                "FD" => S_FD,
                "WL" => S_WL,
                "WH" => S_WH,
                "IX" => S_IX,
                _ => -1,
            }
        }
        if ps.pol_calls_a.len() > 12 {
            return Err(named("policy-call-list-A"));
        }
        for ln in &ps.pol_calls_a {
            if ln.len() < 2 {
                return Err(named("policy-call-list-A"));
            }
            let mut l = crate::verifier::attention_shape::Line::default();
            l.name = ln[0].clone();
            l.kind = ln[1].clone();
            if l.kind != "KR" && l.kind != "KFD" && l.kind != "R16" && l.kind != "WH" {
                return Err(named("policy-call-list-A"));
            }
            if lines.iter().any(|o| o.name == l.name) {
                return Err(named("policy-call-list-A"));
            }
            for s in &ln[2..] {
                let v = seg_of(s);
                if v < 0 {
                    return Err(named("policy-call-list-A"));
                }
                l.segs.push(v);
            }
            lines.push(l);
        }
        if lines.is_empty() {
            return Err(named("policy-call-list-A"));
        }
        {
            let nms = ["RM", "RD", "FM", "FD", "WL", "WH", "IX"];
            let mut s = String::new();
            for l in &lines {
                s.push_str(&format!("callA {} {}", l.name, l.kind));
                for g in &l.segs {
                    s.push(' ');
                    s.push_str(nms[*g as usize]);
                }
                s.push('\n');
            }
            let w = pack_words(&s);
            let mut hh = [0u32; DW as usize];
            earlier_hash_h_digest(&mut hh, 73, &w, w.len() as u64, 1, calls);
            lay_words(&mut ps, h.off_h_calls_a, &hh)?;
        }
        if h.gk & (h.gk - 1) != 0 {
            return Err(named("af-shape-heads"));
        }
        if h.lmh < h.lt || h.lmh > 24 || h.lmo < h.lt || h.lmo > 24 || h.lmba > 24
            || h.lms > 24 || h.nas == 0 || h.nas > 64
        {
            return Err(named("shape-request-matrix-A"));
        }
        for g in 0..y.ngr {
            let mut c = ACfg::default();
            c.lt = h.lt as i32;
            c.l_b = h.l_b as i32;
            c.h = h.h;
            c.lgk = ceil_log2(h.gk) as i32;
            c.ldh = y.ldh;
            c.ll = h.ll as i32;
            if h.sx >= 32 {
                return Err(named("af-policy-wd"));
            }
            c.s = h.sx as i32;
            c.rx = h.rx as i32;
            c.k_fd = h.kfd as i32;
            c.lm_s = h.lms as i32;
            c.la = h.la as i32;
            c.lmb = h.lmba as i32;
            c.nmin = h.nmin as i32;
            c.n_as = h.nas as u64;
            c.wc_h = (1u64 << h.lmh) / y.t;
            c.wc_o = (1u64 << h.lmo) / y.t;
            c.wc_q = y.mrow[3] / y.t;
            c.ty = 1u128 << (1 + crate::verifier::common::LBZ);
            c.o_in_qa = true;
            c.lines = lines.clone();
            for lam in 0..y.lam {
                c.sh.push(kl_sh(kl, g * y.lam + lam));
            }
            {
                let mut s = c.sh.clone();
                s.sort_unstable();
                s.dedup();
                let mut n = 0usize;
                for l in &lines {
                    n += if l.kind.as_bytes()[0] == b'K' { s.len() } else { 1 };
                }
                if n > 12 {
                    return Err(named("policy-call-list-A"));
                }
            }
            let mut x = AttentionSubProof::default();
            x.a.cf = c;
            x.input = AttentionSubProofInputs {
                hb,
                gid: (2 + y.ngr + g) as u32,
                kt_o: y.kcol[3],
                col0_q: 0,
                a_o: 2,
                mid_q: tails[g as usize].mats[i_qa].a_id,
                wp_s: 0,
                wp_h: 0,
                wp_o: 0,
                wp_b_a: 0,
                wp_q: 0,
                lidb,
                stated_hb,
                tau: state.tau as u32,
            };
            x.plan()?;
            if h.iotaa0 as u64 != 32 + x.fs.d_t as u64 {
                return Err(named("policy-iotaA"));
            }
            trim_l(&mut x.seam.fp);
            if x.a.fill_q != y.filled[3] || x.a.feat_q != y.feat[3] {
                return Err(Refusal::internal("internal-qa-layout"));
            }
            {
                let mut own_ = vec![
                    (String::from("q"), x.a.at_q),
                    (String::from("kx"), x.a.at_k),
                    (String::from("v"), x.a.at_v),
                    (String::from("o"), x.a.at_o),
                ];
                for t in &y.ten {
                    if t.mat == 3 {
                        own_.push((t.name.clone(), t.at()));
                    }
                }
                let read_ = own_.clone();
                tensors_agree(&own_, &read_)?;
                if x.a.lam != y.lam
                    || x.a.dq != y.dq
                    || x.a.dkv != y.dkv
                    || x.a.ls != y.ls
                    || x.a.dh % y.s2 != 0
                {
                    return Err(named("plan-tensor-layout"));
                }
                if x.a.at_q.j != x.a.cf.h * x.a.dh
                    || x.a.at_o.j != x.a.at_q.j
                    || x.a.at_k.j != x.a.g * x.a.dh
                    || x.a.at_v.j != x.a.at_k.j
                {
                    return Err(named("plan-tensor-layout"));
                }
            }
            ah.push(x);
        }
        {
            let a0 = &ah[0].a;
            let mut w = Vec::with_capacity(a0.u0 as usize);
            for u in 0..a0.u0 as usize {
                w.push(a0.tt[u] as u32);
            }
            let hh = table_digest(&w, calls);
            lay_words(&mut ps, h.off_h_texp, &hh)?;
            if ps.tbl_at == TBLW && hh != ps.tbl_pol[3] {
                return Err(named("table-digest-exp"));
            }
        }
    }
    let reads = reads_of(&y, p3);
    {
        let sz = plan_sizes(&y, &h, &reads);
        if sz.mu_v < 9 || sz.mu_h < 9 || (p3 && sz.mu_h2 < 9) {
            return Err(named("shape-product-layer"));
        }
    }
    let hid_plans = plan_layers(&LayerPlanInputs {
        h: &h,
        y: &y,
        tails: &tails,
        reads: &reads,
        lk_w: ps.frame.block_log,
        lidb,
        hb,
        stated_hb,
        limbs,
    })?;
    // A_g reads qa from G_g's first border array: record the owner's numbers in its plan.
    for g in 0..y.ngr as usize {
        ah[g].seam.tl.border_means(
            0,
            g as i32,
            hid_plans.hid[g].tl.pk_mat.len() as i32,
        )?;
    }
    let hl = build_hl(&h, &y, &ps.pol_calls_h, state)?;
    // The hash of the head's lines `callH`.
    {
        let mut s = String::new();
        for c in &hl.calls {
            s.push_str(&format!("callH {} {}", c.c.name, c.kind));
            for g in &c.segs {
                s.push(' ');
                s.push_str(&g.name);
            }
            s.push('\n');
        }
        let w = pack_words(&s);
        let mut hh = [0u32; DW as usize];
        earlier_hash_h_digest(&mut hh, 73, &w, w.len() as u64, 1, calls);
        lay_words(&mut ps, h.off_h_calls_h, &hh)?;
    }
    let mut ph = plan_head(&HeadPlanInputs {
        h: &h,
        y: &y,
        hl: &hl,
        hid: &hid_plans.hid,
        lk_w: ps.frame.block_log,
        lidb,
        hb,
        stated_hb,
        limbs,
    })?;
    trim_l(&mut ph.fp);
    if y.l_pd + (h.lt as i32) < 9 {
        return Err(named("shape-product-layer-H"));
    }
    let links = build_links(BuildLinksInputs {
        ngr: y.ngr,
        hid: Rc::new(hid_plans.hid),
        ah: Rc::new(ah),
        ph: Rc::new(ph),
        y_fo: &y.fo,
        hl_fs: &hl.fs,
        ws_lay: &ws_lay,
        frame: &ps.frame,
        layout_text,
        tau: state.tau as u64,
    })?;
    let crate::verifier::stage_links::StageLinks {
        links: link_metas,
        identifiers,
        range_checks,
        layout,
        sub,
        hid,
        ah,
        ph,
    } = links;
    // A planning call prints the compact plans after `configure`, so it keeps the sub-proofs. A
    // checking call does not: the clone would hold the attention plans' `Rc` and block their
    // single-owner use in the proof walk.
    let sub_for_plan = if files.plan_only { Some(sub.clone()) } else { None };
    let conf = {
        let cell = core::cell::RefCell::new(Some(shapes_of(
            sub,
            layout,
            identifiers,
            range_checks,
        )));
        let shapes = |_: &[&[u8]], _: &Parameters| -> Shapes {
            cell.borrow_mut()
                .take()
                .expect("configure asks for the shapes once")
        };
        let conf = configure_with_calls(&[pol_b, files.layout.unwrap_or(&[]), &kl_bytes], &shapes, calls);
        conf
    };
    if !conf.refused().is_empty() {
        return Err(named("parameters-not-admitted"));
    }
    let two_codes_h = conf.sized().batch.s.shared_split_needed()
        && conf.sized().once.s.shared_split_needed();
    Ok(Setup {
        ps,
        y,
        hl,
        tails,
        reads,
        ws_lay,
        link_metas,
        hid,
        ah,
        ph,
        conf,
        two_codes_h,
        h_par,
        sub: sub_for_plan,
    })
}

fn read_key_table(conf: &Configured, key: &[u8], first: &mut UnprovedTable) -> Result<()> {
    let mut file = Reader::new(key);
    match read_key_table_unproved_configured(conf, &mut file, first) {
        Ok(()) => Ok(()),
        Err(why) => Err(named(if why.is_empty() { "key-refused" } else { "key-refused" })),
    }
}

fn run_stage_inner(
    mode: StageMode,
    files: &StageFiles<'_>,
    state: &mut StageState,
    calls: &mut HashCalls,
    out: &mut String,
    record: &mut Option<Accounting>,
    work: &mut Option<String>,
) -> Result<i32> {
    let mut st = setup(files, state, calls)?;
    let h = st.ps.h.clone();
    let min_bits = files.asked;
    let below_bar = min_bits < BAR;
    // The commitment ID, from the key file's first bytes, checked for form only. A planning call
    // `-plan accounting` reads no key (`cp_verify.cpp:2328`: `if (ask.keyB)`).
    let mut first = UnprovedTable::default();
    let has_key = !(mode == StageMode::Request && files.plan_only);
    let id_hex = if has_key {
        {
            let mut file = Reader::new(files.key);
            if let Err(why) = read_key_table_unproved_configured(&st.conf, &mut file, &mut first) {
                out.push_str(&format!("key: {}\n", why));
                return Err(named("key-refused"));
            }
        }
        let id = published_id(&st.conf, first.reader(), calls);
        let id_hex = hex_of(id);
        if !files.id_asked.is_empty() && files.id_asked != id_hex {
            return Err(named("model-statement"));
        }
        if mode == StageMode::PlanId {
            // `cp_verify.cpp:2255-2268`: the planning call `id` prints h_par, the IDLINE and ends.
            out.push_str(&format!(
                "h_par={}\n{}{}\nPLAN ONLY: no proof was checked\n",
                crate::verifier::common::hex64(&st.h_par.w),
                crate::verifier::common::IDLINE,
                id_hex
            ));
            return Ok(4);
        }
        if mode == StageMode::Request && !files.plan_only {
            // `cp_verify.cpp:3363`: a request's stage names the leaf table that the proof is about.
            // A planning call prints no such line: cpPlanMain does not pass through the stage lambda.
            out.push_str(&format!("leaf number {}\n", files.entry_number));
        }
        out.push_str(&format!(
            "{}{}\n",
            crate::verifier::common::STAGEIDLINE,
            id_hex
        ));
        id_hex
    } else {
        String::new()
    };
    match mode {
        // `-plan id` has returned above, at its ID line (`cp_verify.cpp:2264-2268`).
        StageMode::PlanId => unreachable!("the planning call id ends at its ID line"),
        StageMode::Key | StageMode::Leaf => {
            let is_key = mode == StageMode::Key;
            let (what, object) = if is_key { ("a key", "key") } else { ("an entry", "leaf") };
            let plan = if is_key { st.conf.key() } else { st.conf.entry() };
            let acct = acct_of(
                &st.conf, plan, what, object, true, min_bits, state, out,
            )?;
            *record = Some(acct.clone());
            let with_work;
            {
                let mut why: Option<&'static str> = None;
                let mut place: Option<&'static str> = None;
                if is_key {
                    let mut tested = TestedTable::default();
                    let verdict = check_key(
                        &st.conf,
                        &mut Reader::new(files.key),
                        &mut tested,
                        calls,
                        &mut why,
                        None,
                        Some(&mut place),
                    );
                    if verdict == crate::frame::configure::ProofVerdict::No {
                        out.push_str(&format!(
                            "key: {}{}{}{}\n",
                            why.unwrap_or("refused"),
                            if place.is_some() { " (" } else { "" },
                            place.unwrap_or(""),
                            if place.is_some() { ")" } else { "" }
                        ));
                        return Err(named("key-refused"));
                    }
                    with_work = verdict == crate::frame::configure::ProofVerdict::YesWithWork;
                } else {
                    let entry = files.entry.unwrap_or(&[]);
                    let mut why: Option<String> = None;
                    let mut place: Option<&'static str> = None;
                    let verdict = check_entry_if_tested(
                        &st.conf,
                        &first,
                        &mut Reader::new(entry),
                        calls,
                        &mut why,
                        None,
                        Some(&mut place),
                    );
                    if verdict == IfTested::No {
                        let w = why.unwrap_or_else(|| String::from("refused"));
                        out.push_str(&format!(
                            "entry: {}{}{}{}\n",
                            w,
                            if place.is_some() { " (" } else { "" },
                            place.unwrap_or(""),
                            if place.is_some() { ")" } else { "" }
                        ));
                        return Err(named("entry-refused"));
                    }
                    with_work = verdict == IfTested::YesWithWorkIfTheTableIsTested;
                }
            }
            if with_work != state.stage_work_note.needed {
                return Err(named("internal-work-two-ways"));
            }
            if !files.quiet {
                out.push_str(&format!(
                    "ok the {}: {} bytes, read to the end\n",
                    if is_key { "key" } else { "entry" },
                    if is_key { files.key.len() } else { files.entry.map(|e| e.len()).unwrap_or(0) }
                ));
            }
            let par_sec = st.conf.parameters().sec;
            let fields = format!(
                " word={} sec={} asked={}",
                state.run_version_word, par_sec, min_bits as i64
            );
            let note = if is_key {
                "research code"
            } else {
                "research code; the key's table was taken on its form alone: what a key says of it is the stage key's to check, on the same bytes"
            };
            let form = if st.two_codes_h { "" } else { SERVED_TWO_CODES };
            let status = last_line(
                out,
                below_bar,
                form,
                crate::consts::LIDB_SEALED,
                0,
                if is_key { "STAGE PASSED: key" } else { "STAGE PASSED: leaf" },
                3,
                &fields,
                note,
                state,
                &acct,
                calls,
            );
            Ok(status)
        }
        StageMode::Request => {
            let t = 1u64 << h.lt;
            if files.odd_statement {
                return Err(named("statement-required"));
            }
            let req = files.request.ok_or_else(|| named("statement-required"))?;
            let yw = files.y.ok_or_else(|| named("statement-required"))?;
            st_from_call(&mut st.ps.so, req, yw, t)?;
            {
                let off = st.ps.h.off_h_tok + DW as usize;
                let yv = st.ps.so.y;
                lay_w(&mut st.ps, off, yv)?;
            }
            st.ps.h = parse_header(&st.ps.st, state)?;
            if st.ps.h.ytok != st.ps.so.y {
                return Err(named("internal-statement-prescan"));
            }
            let vv = st.ps.h.v;
            if st.ps.so.y as u64 >= vv {
                return Err(named("token-range"));
            }
            if st.ps.h.ytok as u64 >= vv {
                return Err(named("header-y"));
            }
            if st.ps.so.req.len() as u64 != t + 2 {
                return Err(named("token-length"));
            }
            let tokv = st.ps.so.req[..t as usize].to_vec();
            {
                let mut hh = [0u32; DW as usize];
                th(&mut hh, &st.ps.so.req, calls);
                let off = st.ps.h.off_h_tok;
                lay_words(&mut st.ps, off, &hh)?;
            }
            let row_r = st.ps.so.req[t as usize] as u64;
            let row_e = st.ps.so.req[t as usize + 1] as u64;
            if row_r >= row_e || row_e > t {
                return Err(named("statement-range"));
            }
            for v in &tokv {
                if *v as u64 >= vv {
                    return Err(named("token-range"));
                }
            }
            if row_r >= row_e || row_e > t {
                return Err(named("statement-range"));
            }
            let mut win = vec![0u32; t as usize];
            let mut on = vec![false; t as usize];
            let mut on_c = vec![false; t as usize];
            let mut hrc = 0u64;
            for pos in row_r..row_e {
                on[pos as usize] = true;
                win[pos as usize] = if pos + 1 < t {
                    tokv[(pos + 1) as usize]
                } else {
                    st.ps.h.ytok
                };
                on_c[pos as usize] = pos + 1 < t;
                if pos + 1 < t {
                    hrc += 1;
                }
            }
            // The leaf table on which the proof was made, for form only. A planning call reads no
            // proof and no entry (`cp_verify.cpp:2331`: `if (!planOnly)`).
            let mut further = UnprovedTable::default();
            if !files.plan_only {
                let entry = files.entry.ok_or_else(|| named("internal-cp-cut"))?;
                let mut file = Reader::new(entry);
                if let Err(why) =
                    read_entry_table_unproved_configured(&st.conf, &mut file, &mut further)
                {
                    out.push_str(&format!("entry: {}\n", why));
                    return Err(named("entry-refused"));
                }
            }
            for i in 0..st.ps.st.len() {
                if !st.ps.so.laid[i] {
                    return Err(named("internal-statement-cover"));
                }
            }
            if !files.quiet {
                out.push_str("ok the request's form; key's and entry's tables read for their form alone\n");
            }
            acct_of(
                &st.conf,
                st.conf.proof(),
                "a proof",
                "request",
                false,
                min_bits,
                state,
                out,
            )?;
            {
                let set = st.conf.sized().d.set.clone();
                let all = merged(
                    &set,
                    &[
                        st.conf.key().clone(),
                        st.conf.entry().clone(),
                        st.conf.proof().clone(),
                    ],
                );
                *record = Some(account(&all, -1));
            }
            // The conditions of the standard parameter form.
            let mut one_shift = true;
            for l in 0..h.l as u64 {
                one_shift = one_shift && kl_sh(files.kl, l) == kl_sh(files.kl, l - l % st.y.lam);
            }
            let mut norm_shifts = h.kf <= h.mf;
            for l in 0..h.l as u64 {
                norm_shifts = norm_shifts
                    && kl_at(files.kl, l, 8) <= kl_at(files.kl, l, 7)
                    && kl_at(files.kl, l, 10) <= kl_at(files.kl, l, 9);
            }
            let mut one_placement = true;
            for l in 0..st.link_metas.len() {
                if st.link_metas[l].kind != crate::verifier::segments::LinkKind::Layers {
                    continue;
                }
                let px_mat = {
                    let p = &st.hid[st.link_metas[l].g as usize];
                    p.tl.px_mat.clone()
                };
                let px0 = st.hid[0].tl.px_mat.clone();
                one_placement = one_placement && px_mat.len() == px0.len();
                let mut i = 0;
                while one_placement && i < px_mat.len() {
                    let a = st.conf.fixed().layout.find(l, &format!("M{}", px_mat[i]));
                    let b = st.conf.fixed().layout.find(0, &format!("M{}", px0[i]));
                    one_placement = placed_alike(a, b);
                    i += 1;
                }
            }
            let not_served = served_form(&Served {
                experts: h.ne > 0,
                five_limbs: state.residual_stream_limbs == 5,
                clamps: state.rcl != 0 && state.gcl != 0,
                prompt_source: h.toksrc == 1,
                placement_table: files.layout.is_some(),
                table_digests: st.ps.tbl_at == TBLW,
                no_range_words: !st.ps.eg_seen && !st.ps.smax_seen,
                three_bytes: h.sx < 32,
                ring_degree: h.dd == 2048,
                one_shift,
                one_placement,
                softmax_table: h.sx == 12 && h.rx == 8,
                rotary_table: rotary_served(h.theta0, h.dh, h.lt as u64),
                norm_shifts,
                two_codes: st.two_codes_h,
                next_token: !files.next_token_asked
                    || (row_r + 1 == t && row_e == t),
                exact_match: files.plan_only
                    || files.policy.given
                    || hrc == 0
                    || acceptance_policy_is_exact_match(
                        h.clipc as u64,
                        h.theta as u64,
                        h.cap as u64,
                        h.digsh as u64,
                        h.tabs as u64,
                    ),
                policy_named: !files.policy.given
                    || files.policy.is(
                        h.clipc as u64,
                        h.theta as u64,
                        h.cap as u64,
                        h.logs as u64,
                        h.digsh as u64,
                        h.tabs as u64,
                    ),
            });
            if files.plan_only {
                // `planEndH` (`cp_verify.cpp:2435-2461`): the plan, the profile, the two one-time
                // lines, the not-served conditions, h_par and the configuration digest; status 4.
                return plan_end(out, &st, &h, &not_served, state);
            }
            // The proof.
            let proof = files.proof.ok_or_else(|| named("internal-cp-cut"))?;
            let mut st_no_reply = st.ps.st.clone();
            st_no_reply[state.stated_target.at - 1] = 0;
            let request_b = words_bytes(&st_no_reply);
            let file_words = words_bytes(&st.ps.so.req);
            let reply = E::from_base(F::from_u64(st.ps.so.y as u64));
            let mut facts = ProofFacts::default();
            let mut why: Option<&'static str> = None;
            let mut err: Option<Refusal> = None;
            let ah_slice: &mut [AttentionSubProof] =
                Rc::get_mut(&mut st.ah).expect("the attention plans are shared");
            let mut env = SegRun {
                links: &st.link_metas,
                hid: &st.hid,
                ah: ah_slice,
                ph: &st.ph,
                h: &st.ps.h,
                y: &st.y,
                hl: &st.hl,
                reads: &st.reads,
                ws_lay: &st.ws_lay,
                kl: files.kl,
                ngr: st.y.ngr,
                p3: st.ps.h.ne > 0,
                lidb: state.lidb,
                limbs: state.residual_stream_limbs,
                gcl: state.gcl,
                rcl: state.rcl,
                tokens: &tokv,
                y_tok: st.ps.so.y,
                win: &win,
                on: &on,
                on_c: &on_c,
                hrc,
            };
            let mut cb = |v: &mut crate::iop::context::VerifierContext<'_, '_, '_, '_>,
                          x: &RequestPublic,
                          r: &mut LinksResult,
                          c2: &mut HashCalls|
             -> bool {
                match run_links(v, x, r, &mut env, true, c2) {
                    Ok(()) => true,
                    // `ChainCheck::first()`/`finish()` false: `check_proof` reads the channel's
                    // reason and the stage prints it as `proof: <why>`.
                    Err(LinkStop::False) => false,
                    Err(LinkStop::Refusal(e)) => {
                        err = Some(e);
                        false
                    }
                }
            };
            let verdict = check_proof_if_tested(
                &st.conf,
                &further,
                files.entry_number,
                &request_b,
                &file_words,
                &reply,
                &mut Reader::new(proof),
                &mut cb,
                None,
                calls,
                &mut why,
                Some(&mut facts),
                None,
            );
            if let Some(e) = err {
                return Err(e);
            }
            if verdict == IfTested::No {
                let w = why.unwrap_or("refused");
                out.push_str(&format!("proof: {}\n", w));
                return Err(named(if w == "the proof is about another reply" {
                    "reply-differs"
                } else {
                    "proof-refused"
                }));
            }
            if (verdict == IfTested::YesWithWorkIfTheTableIsTested)
                != state.stage_work_note.needed
            {
                return Err(named("internal-work-two-ways"));
            }
            out.push_str(&format!(
                "seal {}\nweight hiding: NOT CHECKED BY THIS RUN (it rests on how the commitment was made)\n",
                hex_of(facts.seal)
            ));
            let stated_w = format!(
                " T={} lim=- C={} theta={} cap={} s={} sh={} sT={} F={}",
                t, h.clipc, h.theta, h.cap, h.logs, h.digsh, h.tabs, h.famf
            );
            let par_sec = st.conf.parameters().sec;
            let par_slots = st.conf.parameters().slots;
            let fields = format!(
                " word={} ms={} sec={} t={} asked={} by=largest-round-error{} leaves={} place={} card=0 judged=1 of 1 dj={} build={} dw={}",
                state.run_version_word,
                id_hex,
                par_sec,
                st.conf.sized().d.link.t,
                min_bits as i64,
                stated_w,
                par_slots,
                facts.place,
                hex_of(facts.seal),
                BUILD_SOURCE_DIGEST,
                DW
            );
            let status = last_line(
                out,
                below_bar,
                &not_served,
                state.lidb,
                state.nminh,
                "STAGE PASSED: request",
                3,
                &fields,
                "research code; the test on the weight table was checked",
                state,
                record.as_ref().unwrap(),
                calls,
            );
            *work = if state.stage_work_note.needed {
                Some(format!(
                    "{:.2} + {} (one round's error without its work, in bits, + its bits of work; {})",
                    libm::floor(100.0 * state.stage_work_note.bits) / 100.0,
                    state.stage_work_note.work,
                    state.stage_work_note.where_
                ))
            } else {
                None
            };
            Ok(status)
        }
    }
}

/// Runs one stage; see the module comment.
pub fn run_stage(mode: StageMode, files: StageFiles<'_>, state: &mut StageState) -> StageOutcome {
    let mut calls = HashCalls::new();
    let mut out = String::new();
    let mut record: Option<Accounting> = None;
    let mut work: Option<String> = None;
    let status = match run_stage_inner(
        mode,
        &files,
        state,
        &mut calls,
        &mut out,
        &mut record,
        &mut work,
    ) {
        Ok(s) => s,
        Err(Refusal::Named(n)) => {
            out.push_str(&format!("NO: {}\n", n));
            1
        }
        Err(Refusal::Internal(n)) => {
            out.push_str(&format!("NOT CHECKED: {}\n", n));
            5
        }
    };
    StageOutcome { status, text: out, calls: calls.total(), acct: record, work }
}
