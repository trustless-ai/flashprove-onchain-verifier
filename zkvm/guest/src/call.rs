//! The whole call inside the guest: the three stages (`fp_core::verifier::run_stage`) and the
//! parent's assembly (`cpStagesRun`, `cpCovered`, the `result-v1` line), adapted from
//! `rust-nostd-verifier/fp-host/src/main.rs` so that the public output's lines match the host's
//! byte for byte. Only the pass path is assembled in full; the S5 gate is the accepted example.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use fp_core::consts::{BUILD_SOURCE_DIGEST, DW, HEXW};
use fp_core::frame::heads::configuration_digest;
use fp_core::hash::calls::HashCalls;
use fp_core::numbers::accounting::Accounting;
use fp_core::numbers::accounting_print::print_accounting;
use fp_core::numbers::real::cut2;
use fp_core::out::cp_line_of;
use fp_core::stage_state::StageState;
use fp_core::verifier::common::{
    above_clip, acceptance_policy_is_exact_match, policy_kind, PolicyNamed, RESULTWORD, STAGEIDLINE,
};
use fp_core::verifier::run_stage::{run_stage, StageFiles, StageMode};

/// The call's private input: the files, the proof's leaf number and the commitment ID.
pub struct Inputs<'a> {
    pub pol: &'a [u8],
    pub layout: &'a [u8],
    pub kl: &'a [u8],
    pub key: &'a [u8],
    pub entry: &'a [u8],
    pub entry_number: u32,
    pub request: &'a [u8],
    pub y: &'a [u8],
    pub proof: &'a [u8],
    pub id_asked: &'a str,
    pub asked: f64,
    /// 0: the whole call; 1: the key stage alone; 2: the leaf stage alone; 3: the request stage
    /// alone. A partial run only measures that stage; its public output is the stage's text.
    pub part: u32,
}

/// One stage's output (`RanStage` in fp-host).
struct RanStage {
    name: &'static str,
    status: i32,
    text: String,
    calls: u64,
    acct: Option<Accounting>,
}

/// What `cpCovered()` returns, the parts that the line for programs uses.
struct Covered {
    policy: String,
    fields: String,
    claim: &'static str,
    other_kind: bool,
    kind_taken: bool,
}

fn words(b: &[u8]) -> Vec<u32> {
    b.chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

fn last_text_line(out: &str) -> String {
    let mut last = out;
    if let Some(x) = last.strip_suffix('\n') {
        last = x;
    }
    match last.rfind('\n') {
        Some(nl) => String::from(&last[nl + 1..]),
        None => String::from(last),
    }
}

fn first_hexw(s: String) -> String {
    if s.len() > HEXW {
        String::from(&s[..HEXW])
    } else {
        s
    }
}

fn work_pair_of(s: &str) -> Option<(f64, u32)> {
    let plus = s.find('+')?;
    let bits: f64 = s[..plus].trim().parse().ok()?;
    let rest = s[plus + 1..].trim_start();
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    if digits.is_empty() {
        return None;
    }
    Some((bits, digits.parse().ok()?))
}

/// `cpCovered()` (`cp_verify.cpp:2968-3007`).
fn cp_covered(request: &[u32], leaf: u32, result: &str) -> Option<Covered> {
    if request.len() < 3 {
        return None;
    }
    let t_len = request.len() as u64 - 2;
    let r = request[t_len as usize] as u64;
    let e = request[t_len as usize + 1] as u64;
    if r >= e || e > t_len {
        return None;
    }
    let field = |name: &str| -> Option<u64> {
        let key = format!(" {}=", name);
        let at = result.find(&key)?;
        let b = result.as_bytes();
        let mut i = at + key.len();
        let first = i;
        let mut v = 0u64;
        while i < b.len() && b[i].is_ascii_digit() && i - first < 18 {
            v = 10 * v + (b[i] - b'0') as u64;
            i += 1;
        }
        if i > first && i < b.len() && b[i] == b' ' {
            Some(v)
        } else {
            None
        }
    };
    let c = field("C")?;
    let theta = field("theta")?;
    let cap = field("cap")?;
    let s = field("s")?;
    let sh = field("sh")?;
    let st = field("sT")?;
    let f = field("F")?;
    let last = core::cmp::min(e, t_len - 1);
    let kind = policy_kind(c, theta, cap, s, sh, st);
    let policy = format!(
        "{} C={} theta={} cap={} s={} sh={}",
        kind, c, theta, cap, s, sh
    );
    let other_kind = r + 1 <= last && !acceptance_policy_is_exact_match(c, theta, cap, sh, st);
    let claim = if r + 1 > last {
        "next-token"
    } else if other_kind {
        "policy"
    } else {
        "exact-match"
    };
    let tokens = if r + 1 <= last {
        format!("{}..{}", r + 1, last)
    } else {
        String::from("none")
    };
    let y = if e == t_len { "yes" } else { "no" };
    let fields = format!(
        "r={} e={} T={} tokens={} y={} policy={} C={} theta={} cap={} s={} sh={} sT={} F={} above-clip={} leaf={}",
        r,
        e,
        t_len,
        tokens,
        y,
        kind,
        c,
        theta,
        cap,
        s,
        sh,
        st,
        f,
        above_clip(last - r, c, theta, cap, sh),
        leaf
    );
    Some(Covered {
        policy,
        fields,
        claim,
        other_kind,
        kind_taken: st + 4 == sh,
    })
}

/// Runs the call and returns (public output, exit status). The output is what `fp-host` prints
/// between the `---- the call ----` line and the verdict: the accounting, then `result-v1`, then
/// the verdict.
pub fn run(input: Inputs<'_>) -> (String, i32) {
    if input.kl.len() % 4 != 0 {
        return (String::from("NO: KL-length\n"), 1);
    }
    let kl = words(input.kl);
    let request_words = words(input.request);
    let y_words = words(input.y);
    // `hParOf`'s configuration digest: only its hash calls enter the call's record.
    let mut host_calls = HashCalls::new();
    let _h_par = configuration_digest(&[input.pol, input.layout, input.kl], &mut host_calls);
    let policy = PolicyNamed::default();
    if input.part != 0 {
        // S5a-3's per-stage measurement: one stage in this execution.
        let (mode, entry, req, yy, proof): (
            StageMode,
            Option<&[u8]>,
            Option<&[u32]>,
            Option<&[u32]>,
            Option<&[u8]>,
        ) = match input.part {
            1 => (StageMode::Key, None, None, None, None),
            2 => (StageMode::Leaf, Some(input.entry), None, None, None),
            _ => (
                StageMode::Request,
                Some(input.entry),
                Some(&request_words),
                Some(&y_words),
                Some(input.proof),
            ),
        };
        let request_mode = mode == StageMode::Request;
        let files = StageFiles {
            pol: input.pol,
            layout: Some(input.layout),
            kl: &kl,
            key: input.key,
            entry,
            entry_number: if request_mode { input.entry_number } else { 0 },
            request: req,
            y: yy,
            odd_statement: false,
            proof,
            id_asked: input.id_asked,
            asked: input.asked,
            quiet: true,
            next_token_asked: false,
            plan_only: false,
            policy: &policy,
        };
        let mut state = StageState::default();
        state.inner_threads = 1;
        let out = run_stage(mode, files, &mut state);
        return (out.text, out.status);
    }
    let specs: [(StageMode, Option<&[u8]>, Option<&[u32]>, Option<&[u32]>, Option<&[u8]>); 3] = [
        (StageMode::Key, None, None, None, None),
        (StageMode::Leaf, Some(input.entry), None, None, None),
        (
            StageMode::Request,
            Some(input.entry),
            Some(&request_words),
            Some(&y_words),
            Some(input.proof),
        ),
    ];
    let mut run: Vec<RanStage> = Vec::with_capacity(specs.len());
    for (mode, entry, req, yy, proof) in specs {
        let request_mode = mode == StageMode::Request;
        let files = StageFiles {
            pol: input.pol,
            layout: Some(input.layout),
            kl: &kl,
            key: input.key,
            entry,
            entry_number: if request_mode { input.entry_number } else { 0 },
            request: req,
            y: yy,
            odd_statement: false,
            proof,
            id_asked: input.id_asked,
            asked: input.asked,
            quiet: true,
            next_token_asked: false,
            plan_only: false,
            policy: &policy,
        };
        let mut state = StageState::default();
        state.inner_threads = 1;
        let out = run_stage(mode, files, &mut state);
        run.push(RanStage {
            name: mode.name(),
            status: out.status,
            text: out.text,
            calls: out.calls,
            acct: out.acct,
        });
    }
    let mut no = String::new();
    let mut failed = String::new();
    let mut call = Accounting::default();
    let mut calls_all = 0u64;
    let mut one_time_assumed = 0u64;
    let mut counted_all = true;
    let mut accts_read = 0usize;
    let mut not_a_verification = false;
    let mut work_stage = false;
    let mut work_pair = String::new();
    let mut work_least = 0.0f64;
    for (i, st) in run.iter().enumerate() {
        let last = last_text_line(&st.text);
        let mut own = st.acct.clone();
        if let Some(a) = own.as_mut() {
            a.counted = true;
            a.calls = st.calls;
            calls_all += a.calls;
            counted_all = counted_all && a.counted;
            if i + 1 < run.len() {
                one_time_assumed += a.closeness[1];
            }
            call = a.clone();
            accts_read += 1;
        }
        let wl = cp_line_of(&st.text, "work: ");
        let mut work_read = false;
        if let Some(par) = wl.find(" (") {
            if let Some((b, g)) = work_pair_of(&wl[..par]) {
                if (1..=fp_core::verifier::common::WORK_BITS_MOST).contains(&g) {
                    work_read = true;
                    if work_pair.is_empty() || b < work_least {
                        work_least = b;
                        work_pair = String::from(&wl[..par]);
                    }
                }
            }
        }
        if st.status == 12 {
            work_stage = true;
        }
        if st.status == 14 {
            not_a_verification = true;
        }
        if st.status == 1 && last.starts_with("NO: ") && last.len() > 4 {
            if no.is_empty() {
                no = String::from(&last[4..]);
            }
        } else if !(st.status == 3
            && !work_read
            && last == format!("STAGE PASSED: {}", st.name))
            && !(st.status == 12
                && work_read
                && last == format!("STAGE PASSED WITH WORK: {}", st.name))
            && st.status != 14
            && failed.is_empty()
        {
            failed = format!("the stage {} ended with status {}", st.name, st.status);
        }
    }
    if !no.is_empty() {
        return (format!("NO: {}\n", no), 1);
    }
    if !failed.is_empty() || accts_read != run.len() {
        return (String::from("NOT CHECKED: internal-sums-line\n"), 5);
    }
    let id_hex = first_hexw(cp_line_of(&run[0].text, STAGEIDLINE));
    if id_hex.len() != HEXW {
        return (String::from("NOT CHECKED: internal-id-two-ways\n"), 5);
    }
    for st in &run {
        if first_hexw(cp_line_of(&st.text, STAGEIDLINE)) != id_hex {
            return (String::from("NOT CHECKED: internal-id-two-ways\n"), 5);
        }
    }
    // Adds the parent's own hash calls.
    call.counted = counted_all;
    call.calls = calls_all + host_calls.total();
    let covered = match cp_covered(
        &request_words,
        input.entry_number,
        &cp_line_of(&run[run.len() - 1].text, "result:"),
    ) {
        Some(c) => c,
        None => return (String::from("NOT CHECKED: internal-covered-line\n"), 5),
    };
    let work_agrees = work_stage == call.needs_work
        && (!work_stage || {
            match work_pair.find(" + ") {
                Some(plus) => {
                    (work_least - call.lists.bits).abs() < 0.0101
                        && String::from(&work_pair[plus..]) == format!(" + {}", call.lists.work)
                }
                None => false,
            }
        });
    if work_stage != !work_pair.is_empty() || !work_agrees {
        return (String::from("NOT CHECKED: internal-sums-line\n"), 5);
    }
    if !covered.kind_taken {
        return (String::from("NOT CHECKED: internal-policy-kind\n"), 5);
    }
    let mut most_work = 0u32;
    for kind in &call.work {
        for &g in kind {
            most_work = core::cmp::max(most_work, g);
        }
    }
    let status = if not_a_verification { 14 } else { 0 };
    let mut out = String::new();
    out.push_str(&print_accounting(
        &call,
        "key, entry and proof",
        false,
        6,
    ));
    out.push_str(&format!(
        "{} status={} claim={} id={} bits={:.0} work={} work-rounds={} least-round={:.2} least-round-without-work={:.2} commitment-assumed-rounds={} record=1 {} stages=key,leaf,request dw={} build={}\n",
        RESULTWORD,
        status,
        covered.claim,
        id_hex,
        input.asked,
        if call.needs_work { most_work } else { 0 },
        if call.needs_work { call.by_work } else { 0 },
        cut2(call.groups[0].all()),
        cut2(call.lists.bits),
        one_time_assumed,
        covered.fields,
        DW,
        BUILD_SOURCE_DIGEST
    ));
    if not_a_verification {
        out.push_str("NOT-A-VERIFICATION\n");
        return (out, status);
    }
    if covered.other_kind {
        out.push_str(&format!("WITHIN LIMITS: {}\n", covered.policy));
        return (out, status);
    }
    out.push_str("YES\n");
    (out, status)
}
