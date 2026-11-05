//! Host shell for the verifier: the command line, file reading, the two header checks and the
//! assembly of a whole call (`cpMain`, `cpStagesRun` and `cpCovered`).
//!
//! The three stages run in this process, each on a fresh `StageState`; their texts are joined into
//! the call's output exactly as the reference program prints them. The C++ source of each piece is
//! named in the comments. CLI text is taken from `verifier/src/cp_verify.cpp:3015-3115`; the static
//! part is `usage.txt`, captured from the reference binary so that the bytes match.

use std::env;
use std::ffi::CStr;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::os::raw::c_char;
use std::process::exit;
use std::time::Instant;

use fp_core::consts::{
    BAR, BUILD_SOURCE_DIGEST, DIGEST_HALF_BITS, DW, HEXW, STATUS_NOT_A_VERIFICATION,
    STATUS_NOT_CHECKED,
};
use fp_core::frame::heads::configuration_digest;
use fp_core::frame::parameters::pol_word_u64;
use fp_core::hash::calls::HashCalls;
use fp_core::head::{cp_key_head, cp_policy_word, cp_proof_head};
use fp_core::numbers::accounting::Accounting;
use fp_core::numbers::accounting_print::print_accounting;
use fp_core::numbers::real::cut2;
use fp_core::out::{
    cp_line_of, cp_not_checked_lines, cp_reason_of, input_unreadable_line, no_line, role_name,
};
use fp_core::refusal::Refusal;
use fp_core::stage_state::StageState;
use fp_core::verifier::common::{
    above_clip, acceptance_policy_is_exact_match, hex64, internal_name, policy_empty, policy_kind,
    policy_named_read, reject_long_text_file, PolicyNamed, COMMITMENTLINE, IDHIDDEN, IDLINE,
    NOT_A_VERIFICATION_TEXT, RECORDCLAUSE, RESULTWORD, STAGEIDLINE, WITHIN, WORKLINE,
    WORK_BITS_MOST,
};
use fp_core::verifier::run_stage::{run_stage, StageFiles, StageMode};

const USAGE: &str = include_str!("usage.txt");

/// `POLICY_OPTION_FORM_TEXT` (`vf_common.h:683-686`).
const POLICY_OPTION_FORM_TEXT: &str = "-policy requires <kind>,<C>,<theta>,<cap>,<s>,<sh>: exact-match or clipped-gap and five whole numbers of at most ten digits without leading zeros, with commas and no blanks between them";

/// `ASKED_FORM` (`cp_verify.cpp:3011`).
const ASKED_FORM: &str = "<asked>, the requested bits, is a whole number from 0 to 1000000, in digits alone, without a leading zero";

/// `THREADS_FORM` (`cp_verify.cpp:3012`).
const THREADS_FORM: &str =
    "after -j comes a whole number from 1 to 256, in digits alone, without a leading zero";

fn main() {
    let args: Vec<String> = env::args().collect();
    exit(cp_main(&args));
}

/// `cpMain()` (`cp_verify.cpp:3274-3389`), S1 subset.
fn cp_main(args: &[String]) -> i32 {
    let arg1 = args.get(1).map(String::as_str).unwrap_or("");
    if arg1 == "-plan" {
        return plan_main(args);
    }
    let key_part = arg1 == "-key";
    let leaf_part = arg1 == "-leaf";
    let first = if key_part || leaf_part { 2 } else { 1 };
    let places = if key_part {
        2
    } else if leaf_part {
        3
    } else {
        5
    };
    if args.len() < first + places {
        usage(&format!(
            "too few arguments: this call wants {} file and folder names",
            places
        ));
    }
    let at = &args[first..first + places];

    let mut bits_arg: Option<&str> = None;
    let mut j_arg: Option<&str> = None;
    let mut id_arg: Option<&str> = None;
    let mut quiet = false;
    let mut next_token_asked = false;
    let mut show_stages = false;
    let mut no_work = false;
    let mut policy = PolicyNamed::default();

    let mut i = first + places;
    while i < args.len() {
        if args[i] == "-bits" && bits_arg.is_none() && i + 1 < args.len() {
            i += 1;
            bits_arg = Some(&args[i]);
        } else if args[i] == "-id" && id_arg.is_none() && i + 1 < args.len() {
            i += 1;
            id_arg = Some(&args[i]);
        } else if args[i] == "-j" && j_arg.is_none() && i + 1 < args.len() {
            i += 1;
            j_arg = Some(&args[i]);
        } else if args[i] == "-q" {
            quiet = true;
        } else if args[i] == "-show-stages" {
            show_stages = true;
        } else if args[i] == "-no-proof-of-work" {
            no_work = true;
        } else if args[i] == "-next-token" && !key_part && !leaf_part {
            next_token_asked = true;
        } else if args[i] == "-policy"
            && !policy.given
            && !key_part
            && !leaf_part
            && i + 1 < args.len()
        {
            i += 1;
            match policy_named_read(&args[i]) {
                Some(p) => policy = p,
                None => {
                    eprintln!("{}", POLICY_OPTION_FORM_TEXT);
                    return 2;
                }
            }
        } else {
            usage(&format!(
                "argument {} is not an option of this call, comes a second time, or lacks its value",
                i
            ));
        }
        i += 1;
    }

    let mut asked = BAR;
    if let Some(arg) = bits_arg {
        match decimal(arg, 1_000_000) {
            Some(v) => asked = v as f64,
            None => usage(&format!("after -bits comes <asked>; {}", ASKED_FORM)),
        }
    }
    let mut threads: u32 = 1;
    if let Some(arg) = j_arg {
        match decimal(arg, 256) {
            Some(v) if v != 0 => threads = v,
            _ => usage(THREADS_FORM),
        }
    }

    let mut id_asked = id_arg.unwrap_or("").as_bytes().to_vec();
    for c in &mut id_asked {
        if (b'A'..=b'F').contains(c) {
            *c += b'a' - b'A';
        }
    }
    let id_asked = String::from_utf8(id_asked).unwrap_or_default();
    if id_arg.is_some()
        && (id_asked.len() != HEXW
            || !id_asked
                .bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)))
    {
        eprintln!("-id requires {} hex digits", HEXW);
        return 2;
    }

    let below_bar = !(asked >= BAR);
    if asked > DIGEST_HALF_BITS {
        end_with_refusal(Refusal::named("cp-bits-above-digest"), "");
    }
    // `cpPolicySays(policy, 0, 0)`: the numbers alone, before any file is opened.
    policy_says(&policy, 0, 0);

    let conf = cp_conf_read(&at[0]);
    let key_path = if key_part || leaf_part {
        at[1].clone()
    } else {
        format!("{}/key.bin", at[1])
    };
    let key_b = need_bytes(&key_path, "key");

    // `hParOf()` (`cp_verify.cpp:843-851`): the configuration digest of the three public files,
    // printed as `h_par=` and compared with nothing. Its hash calls are the parent call's own.
    if let Err(r) = reject_long_text_file(conf.pol.len() as u64) {
        end_with_refusal(r, "");
    }
    if conf.kl.len() < DW as usize {
        end_with_refusal(Refusal::named("KL-length"), "");
    }
    if let Some(l) = &conf.layout {
        if let Err(r) = reject_long_text_file(l.len() as u64) {
            end_with_refusal(r, "");
        }
    }
    let kl_bytes = words_bytes(&conf.kl);
    let mut host_calls = HashCalls::new();
    let h_par = hex64(
        &configuration_digest(
            &[&conf.pol, conf.layout.as_deref().unwrap_or(&[]), &kl_bytes],
            &mut host_calls,
        )
        .w,
    );

    let pol_ver = match cp_policy_word(&conf.pol) {
        Ok(v) => v,
        Err(r) => end_with_refusal(r, ""),
    };
    if let Err(r) = cp_key_head(&key_b, pol_ver) {
        end_with_refusal(r, "");
    }

    let mut entry_b: Option<Vec<u8>> = None;
    let mut request_words: Option<Vec<u32>> = None;
    let mut y_words: Option<Vec<u32>> = None;
    let mut odd_statement = false;
    let mut proof_b: Option<Vec<u8>> = None;
    let mut entry_number: u32 = 0;
    if leaf_part {
        entry_b = Some(need_bytes(&at[2], "entry"));
    } else if !key_part {
        // `cpLengthHeld()` uses the parameter file's `lt` when present. Like C++'s polWord(), the
        // strict parser strips the frame first.
        if let Some(lt) = pol_word_u64(&conf.pol, "lt") {
            if lt <= 20 {
                cp_length_held(&at[2], (1u64 << lt) + 2);
            }
        }
        cp_length_held(&at[3], 1);
        let (request, odd_request) = must_read_words(&at[2], "request");
        let (y, odd_y) = must_read_words(&at[3], "y");
        odd_statement = odd_request || odd_y;
        if !odd_statement {
            cp_policy_held(&policy, &conf.pol, &request);
        }
        let proof = need_bytes(&at[4], "proof");
        let k = match cp_proof_head(&proof, pol_ver) {
            Ok(k) => k,
            Err(r) => end_with_refusal(r, ""),
        };
        entry_number = k;
        let leaf_path = format!("{}/leaf/{}.bin", at[1], k);
        // C++ uses readWholeFile() here and turns any failure into cp-entry-missing, not into
        // input-unreadable-entry (`cp_verify.cpp:3373-3374`).
        match read_regular_file(&leaf_path) {
            Ok(b) => entry_b = Some(b),
            Err(_) => end_with_refusal(Refusal::named("cp-entry-missing"), ""),
        }
        request_words = Some(request);
        y_words = Some(y);
        proof_b = Some(proof);
    }

    // The stages (`stageOn` in cpMain; `cpStagesRun`, cp_verify.cpp:2670). C++ forks one child
    // per stage; the port runs them in this process, each on a fresh `StageState`.
    let few = core::cmp::max(1, threads / 8);
    let specs: Vec<(StageMode, u32)> = if key_part {
        vec![(StageMode::Key, threads)]
    } else if leaf_part {
        vec![(StageMode::Leaf, threads)]
    } else {
        vec![(StageMode::Key, few), (StageMode::Leaf, few), (StageMode::Request, threads)]
    };
    let default_policy = PolicyNamed::default();
    let mut run: Vec<RanStage> = Vec::with_capacity(specs.len());
    for &(mode, stage_threads) in &specs {
        let request_mode = mode == StageMode::Request;
        let files = StageFiles {
            pol: &conf.pol,
            layout: conf.layout.as_deref(),
            kl: &conf.kl,
            key: &key_b,
            entry: if mode == StageMode::Key { None } else { entry_b.as_deref() },
            entry_number: if request_mode { entry_number } else { 0 },
            request: if request_mode { request_words.as_deref() } else { None },
            y: if request_mode { y_words.as_deref() } else { None },
            odd_statement: request_mode && odd_statement,
            proof: if request_mode { proof_b.as_deref() } else { None },
            id_asked: &id_asked,
            asked,
            quiet,
            next_token_asked: request_mode && next_token_asked,
            plan_only: false,
            policy: if request_mode { &policy } else { &default_policy },
        };
        let mut state = StageState::default();
        state.inner_threads = stage_threads as i32;
        let t = Instant::now();
        let out = run_stage(mode, files, &mut state);
        run.push(RanStage {
            name: mode.name(),
            threads: stage_threads,
            secs: t.elapsed().as_secs_f64(),
            status: out.status,
            text: out.text,
            calls: out.calls,
            acct: out.acct,
        });
    }

    let good = if key_part {
        "PART PASSED: key"
    } else if leaf_part {
        "PART PASSED: leaf"
    } else {
        "YES"
    };
    let good_status = if key_part || leaf_part { 3 } else { 0 };
    stages_run(
        &run,
        good,
        good_status,
        below_bar,
        asked,
        &id_asked,
        !key_part && !leaf_part,
        policy.given,
        show_stages,
        no_work,
        &h_par,
        host_calls,
        request_words.as_deref().unwrap_or(&[]),
        entry_number,
    )
}

/// One stage's output, as `cpStagesRun` keeps it (`Child`).
struct RanStage {
    name: &'static str,
    threads: u32,
    secs: f64,
    status: i32,
    text: String,
    calls: u64,
    acct: Option<Accounting>,
}

/// The last line of a stage's output, without its line feed (`cpStagesRun`, `last`).
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

/// `%g` for the values `asked` takes: whole numbers from 0 to 1000000. C prints the last as
/// `1e+06`, and the others in digits.
fn c_g(v: f64) -> String {
    if v >= 1_000_000.0 {
        return String::from("1e+06");
    }
    format!("{}", v as u64)
}

/// Reads the `%lf + %u` pair of a stage's work line.
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

/// What `cpCovered()` returns (`Covered`, cp_verify.cpp:2606-2614).
struct Covered {
    line: String,
    policy: String,
    fields: String,
    claim: &'static str,
    other_kind: bool,
    kind_taken: bool,
}

/// `cpCovered()` (`cp_verify.cpp:2968-3007`): the line `covered:` and the fields of the line for
/// programs, both built from the request and the request stage's line `result:`.
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
    // `v`: the number after " <name>="; false unless 1 to 18 digits, then a space.
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
    let line = format!(
        "covered: r={} e={} T={} C={} theta={} cap={} s={} sh={} positions={}..{} tokens={} y={} next-token={} policy={} above-clip={} (places in the request, counted from 0; y=yes: the answer is about y too; it is about nothing else; above-clip: so many of the tokens named by tokens= may cost more than C, and such a token may be any token. It is no limit on the tokens that may be any token: one that costs C or less may be any token too where the committed model's logits lie close together, and no verifier sees that. All costs, each counted as at most C, add up to at most theta times the number of these tokens)\n",
        r,
        e,
        t_len,
        c,
        theta,
        cap,
        s,
        sh,
        r,
        e - 1,
        tokens,
        y,
        if r + 1 == t_len { "yes" } else { "no" },
        kind,
        above_clip(last - r, c, theta, cap, sh)
    );
    let kind_taken = st + 4 == sh;
    Some(Covered { line, policy, fields, claim, other_kind, kind_taken })
}

/// Ends a call under a fault of the verifier's own (`cpNotChecked`, `cp_verify.cpp:2560-2566`).
fn call_not_checked(how: &str, name: &str) -> i32 {
    print!("{}", cp_not_checked_lines(how, name));
    flush_stdout();
    STATUS_NOT_CHECKED
}

/// `cpStagesRun()` (`cp_verify.cpp:2655-2964`): joins the stages' outputs and prints the call's
/// last lines.
#[allow(clippy::too_many_arguments)]
fn stages_run(
    run: &[RanStage],
    good: &str,
    good_status: i32,
    below_bar: bool,
    asked: f64,
    id_asked: &str,
    id_needed: bool,
    policy_given: bool,
    show_stages: bool,
    no_work: bool,
    h_par: &str,
    host_calls: HashCalls,
    request: &[u32],
    leaf: u32,
) -> i32 {
    let id_named = !id_asked.is_empty();
    // A verification call without -id prints IDHIDDEN in place of the files' ID.
    let hide_id = id_needed && !id_named;
    let mut stages_text: Vec<String> = Vec::with_capacity(run.len());
    let mut no = String::new();
    let mut no_stage = String::new();
    let mut no_why = String::new();
    let mut failed = String::new();
    let mut failed_name = String::from("internal-stage");
    let mut causes = String::new();
    let mut call = Accounting::default();
    let mut calls_all = 0u64;
    let mut one_time_assumed = 0u64;
    let mut counted_all = true;
    let mut accts_read = 0usize;
    let mut work_lines = String::new();
    let mut work_pair = String::new();
    let mut work_least = 0.0f64;
    let mut work_stage = false;
    for (i, st) in run.iter().enumerate() {
        // RESULTWORD begins this function's own line. A stage's output that has it is not printed.
        let holds_word = st.text.contains(RESULTWORD);
        if holds_word && failed.is_empty() {
            failed = format!(
                "the output of the stage {} holds the first word of the line for programs, which only the call's closing lines may hold",
                st.name
            );
            failed_name = String::from("internal-result-line");
        }
        let last = last_text_line(&st.text);
        let mut own = st.acct.clone();
        let sums_read = own.is_some();
        if let Some(a) = own.as_mut() {
            // The record as the stage printed it: `acctReadH` reads these two back from the text.
            a.counted = true;
            a.calls = st.calls;
            calls_all += a.calls;
            counted_all = counted_all && a.counted;
            if i + 1 < run.len() {
                one_time_assumed += a.closeness[1];
            }
            call = a.clone();
            accts_read += 1;
            if !((a.target as f64) >= asked) && failed.is_empty() {
                failed = format!(
                    "the target in the record of the stage {} is below the bits asked of the call",
                    st.name
                );
                failed_name = String::from("internal-sums-line");
            }
            if (run.len() == 1 || i + 1 < run.len())
                && (st.status == 3 || st.status == 12)
                && a.needs_work != (st.status == 12)
                && failed.is_empty()
            {
                failed = format!(
                    "the status of the stage {} and its record disagree on work",
                    st.name
                );
                failed_name = String::from("internal-sums-line");
            }
        }
        {
            let shown = if holds_word {
                String::from("not printed: this output holds the first word of the line for programs\n")
            } else {
                st.text.clone()
            };
            let own_id = {
                let s = cp_line_of(&st.text, STAGEIDLINE);
                if s.len() > HEXW {
                    String::from(&s[..HEXW])
                } else {
                    s
                }
            };
            let shown = if hide_id && own_id.len() == HEXW {
                shown.replace(&own_id, IDHIDDEN)
            } else {
                shown
            };
            let mut text = format!(
                "---- stage {} ---- {} thread(s), {:.3} s\n",
                st.name, st.threads, st.secs
            );
            text.push_str(&shown);
            if !shown.is_empty() && !shown.ends_with('\n') {
                text.push('\n');
            }
            stages_text.push(text);
        }
        // A stage's line "work: <bits> + <work> (...)". A stage that ends WITH WORK must have one.
        let wl = cp_line_of(&st.text, "work: ");
        let mut work_read = false;
        if let Some(par) = wl.find(" (") {
            if let Some((b, g)) = work_pair_of(&wl[..par]) {
                if (1..=WORK_BITS_MOST).contains(&g) {
                    work_read = true;
                    work_lines.push_str(&format!("stage {}: work: {}\n", st.name, wl));
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
        if st.status == 1 && last.starts_with("NO: ") && internal_name(&last[4..]) {
            if failed.is_empty() {
                failed = format!("the stage {} met a fault of its own", st.name);
                failed_name = String::from(&last[4..]);
            }
        } else if st.status == 1 && last.starts_with("NO: ") && last.len() > 4 {
            if no.is_empty() {
                no = String::from(&last[4..]);
                no_stage = String::from(st.name);
                no_why = cp_reason_of(&st.text);
            }
        } else if st.status == STATUS_NOT_A_VERIFICATION && last == NOT_A_VERIFICATION_TEXT {
            let res = cp_line_of(&st.text, "result:");
            let why = match res.find("(not a verification: ") {
                Some(c) => String::from(&res[c + 1..]),
                None => String::from("no cause printed"),
            };
            let why = match why.strip_suffix(')') {
                Some(w) => String::from(w),
                None => why,
            };
            causes.push_str(&format!("stage {}: {}\n", st.name, why));
        } else if !(st.status == 3
            && !work_read
            && last == format!("STAGE PASSED: {}", st.name))
            && !(st.status == 12
                && work_read
                && last == format!("STAGE PASSED WITH WORK: {}", st.name))
            && failed.is_empty()
        {
            let how = if st.status == STATUS_NOT_CHECKED {
                String::from(" had no memory or could not start a thread")
            } else {
                format!(
                    " ended with status {} and a last line that does not fit it",
                    st.status
                )
            };
            failed = format!("the stage {}{}", st.name, how);
        } else if !sums_read && failed.is_empty() && st.status != 1 {
            failed = format!("the stage {} printed no record of its accounting", st.name);
            failed_name = String::from("internal-sums-line");
        }
    }
    if no == "model-statement" {
        print!("id: these are not the files of the commitment that you named; nothing in them was checked\nid: take the commitment ID from your own record of where it was published, never from these files\nNO: model-statement\n");
        flush_stdout();
        return 1;
    }
    let may_pass = no.is_empty()
        && failed.is_empty()
        && causes.is_empty()
        && (id_named || !id_needed)
        && !below_bar
        && !fp_core::verifier::common::TEST_BUILD
        && !(no_work && (work_stage || call.needs_work));
    if may_pass || show_stages {
        if no.is_empty() {
            for t in &stages_text {
                print!("{}", t);
            }
        } else {
            for (i, t) in stages_text.iter().enumerate() {
                if run[i].status != 1 {
                    print!("{}", t);
                }
            }
            for (i, t) in stages_text.iter().enumerate() {
                if run[i].status == 1 {
                    print!("{}", t);
                }
            }
        }
    }
    print!("---- the call ----\n");
    if !no.is_empty() {
        print!("refused by the stage {}{}\nNO: {}\n", no_stage, no_why, no);
        flush_stdout();
        return 1;
    }
    if !failed.is_empty() {
        return call_not_checked(&failed, &failed_name);
    }
    let covered = if id_needed {
        let result = cp_line_of(&run.last().map(|s| s.text.as_str()).unwrap_or(""), "result:");
        match cp_covered(request, leaf, &result) {
            Some(c) => Some(c),
            None => {
                return call_not_checked(
                    "the line on the covered positions could not be formed",
                    "internal-covered-line",
                )
            }
        }
    } else {
        None
    };
    if accts_read != run.len() {
        return call_not_checked(
            "a stage's record of its accounting is missing",
            "internal-sums-line",
        );
    }
    // Adds the parent's own hash calls.
    call.counted = counted_all;
    call.calls = calls_all + host_calls.total();
    // The ID is the first stage's, and every stage must have formed the same.
    let id_hex = {
        let s = cp_line_of(&run[0].text, STAGEIDLINE);
        if s.len() > HEXW {
            String::from(&s[..HEXW])
        } else {
            s
        }
    };
    if id_hex.len() != HEXW {
        return call_not_checked("the first stage printed no ID", "internal-id-two-ways");
    }
    for st in run {
        let other = {
            let s = cp_line_of(&st.text, STAGEIDLINE);
            if s.len() > HEXW {
                String::from(&s[..HEXW])
            } else {
                s
            }
        };
        if other != id_hex {
            return call_not_checked("two stages formed two IDs", "internal-id-two-ways");
        }
    }
    if no_work && causes.is_empty() && work_stage != call.needs_work {
        return call_not_checked(
            "the stages' lines on work and the call's record disagree",
            "internal-sums-line",
        );
    }
    if id_named != !id_asked.is_empty() || (id_named && id_asked != id_hex) {
        return call_not_checked(
            "the stages passed under another ID than the caller's",
            "internal-id-two-ways",
        );
    }
    if id_needed && !id_named {
        causes.push_str("the call: not the standard parameter form: id-named (the call named no ID: add -id with the commitment ID)\n");
    }
    if no_work && (work_stage || call.needs_work) {
        causes.push_str(&format!(
            "the call: not the standard parameter form: no-proof-of-work (the call had -no-proof-of-work, and {}{} the parameter file's target only with proof of work counted)\n",
            call.by_work,
            if call.by_work == 1 { " round meets" } else { " rounds meet" }
        ));
    }
    // Names the files as a planning call does (blocks/frame/prints.h).
    let what = if run.len() > 1 {
        "key, entry and proof"
    } else if run[0].name == "key" {
        "the key"
    } else {
        "an entry"
    };
    print!("{}", print_accounting(&call, what, false, 6));
    print!("accounting: asked of this call: {} bits\n", c_g(asked));
    // -key and -leaf print no IDLINE: a committer that copies their output prints at most one.
    let id_line = if covered.is_some() {
        format!(
            "{}{}\n",
            IDLINE,
            if hide_id { IDHIDDEN } else { id_hex.as_str() }
        )
    } else {
        String::new()
    };
    let leaf_key_line = if run.len() == 1 && run[0].name == "leaf" {
        "key: NOT CHECKED BY THIS CALL (its table was taken on its form alone; the part-call -key or a whole call checks it)\n"
    } else {
        ""
    };
    print!(
        "{}{}id: {}\nh_par={}\n{}weight hiding: NOT CHECKED BY THIS CALL (it rests on how the commitment was made)\n{}{}",
        causes,
        id_line,
        if id_named {
            "named by the caller and equal"
        } else {
            "not compared: the call named none"
        },
        h_par,
        leaf_key_line,
        covered.as_ref().map(|c| c.line.as_str()).unwrap_or(""),
        work_lines
    );
    let mut most_work = 0u32;
    for kind in &call.work {
        for &g in kind {
            most_work = core::cmp::max(most_work, g);
        }
    }
    let work_line = if call.needs_work {
        format!(
            "{}up to {} bits counted in {} round{}; with it the least round has {:.2} bits, without it {:.2} bits",
            WORKLINE,
            most_work,
            call.by_work,
            if call.by_work == 1 { "" } else { "s" },
            cut2(call.groups[0].all()),
            cut2(call.lists.bits)
        )
    } else {
        format!("{}none counted", WORKLINE)
    };
    let commitment_line = if covered.is_some() {
        format!(
            "{}{} closeness {} on another source than the bound within a third of the distance{}\n",
            COMMITMENTLINE,
            one_time_assumed,
            if one_time_assumed == 1 {
                "round of the one-time files rests"
            } else {
                "rounds of the one-time files rest"
            },
            RECORDCLAUSE
        )
    } else {
        String::new()
    };
    let result_line = |status: i32| -> String {
        let Some(c) = covered.as_ref() else {
            return String::new();
        };
        format!(
            "{} status={} claim={} id={} bits={:.0} work={} work-rounds={} least-round={:.2} least-round-without-work={:.2} commitment-assumed-rounds={} record=1 {} stages=key,leaf,request dw={} build={}\n",
            RESULTWORD,
            status,
            c.claim,
            if hide_id { IDHIDDEN } else { id_hex.as_str() },
            asked,
            if call.needs_work { most_work } else { 0 },
            if call.needs_work { call.by_work } else { 0 },
            cut2(call.groups[0].all()),
            cut2(call.lists.bits),
            one_time_assumed,
            c.fields,
            DW,
            BUILD_SOURCE_DIGEST
        )
    };
    if !causes.is_empty() || below_bar || fp_core::verifier::common::TEST_BUILD {
        print!("{}{}\n", commitment_line, work_line);
        print!("{}", result_line(STATUS_NOT_A_VERIFICATION));
        print!("{}\n", NOT_A_VERIFICATION_TEXT);
        flush_stdout();
        return STATUS_NOT_A_VERIFICATION;
    }
    // Status 12 (WITH WORK) and a valid line "work:" must come together.
    if work_stage != !work_pair.is_empty() {
        return call_not_checked(
            "a stage's status and its line on work disagree",
            "internal-sums-line",
        );
    }
    // The call's record must agree, on `workPair` too. Both bit figures were truncated: within 0.01.
    if work_stage != call.needs_work || (work_stage && {
        match work_pair.find(" + ") {
            Some(plus) => {
                !((work_least - call.lists.bits).abs() < 0.0101)
                    || String::from(&work_pair[plus..]) != format!(" + {}", call.lists.work)
            }
            None => true,
        }
    }) {
        return call_not_checked(
            "the stages' lines on work and the call's record disagree",
            "internal-sums-line",
        );
    }
    // WITHIN LIMITS is only for a caller that passed -policy.
    if covered.as_ref().map(|c| c.other_kind).unwrap_or(false) && !policy_given {
        return call_not_checked(
            "a call without -policy came as far as WITHIN LIMITS",
            "internal-policy-not-given",
        );
    }
    if covered.is_some() && !covered.as_ref().map(|c| c.kind_taken).unwrap_or(false) {
        return call_not_checked(
            "the parameter file's policy is neither exact-match nor clipped-gap, and no earlier check refused it",
            "internal-policy-kind",
        );
    }
    if let Some(c) = covered.as_ref().filter(|c| c.other_kind) {
        print!("{}{}\n", commitment_line, work_line);
        print!("{}", result_line(0));
        print!("{}{}\n", WITHIN, c.policy);
        flush_stdout();
        return 0;
    }
    print!("{}{}\n", commitment_line, work_line);
    print!("{}", result_line(good_status));
    print!("{}\n", good);
    flush_stdout();
    good_status
}

/// The little-endian bytes of words, as `KL.bin` holds them (`words_bytes`, run_stage.rs).
fn words_bytes(w: &[u32]) -> Vec<u8> {
    let mut o = Vec::with_capacity(4 * w.len());
    for &x in w {
        for i in 0..4 {
            o.push((x >> (8 * i)) as u8);
        }
    }
    o
}

/// A `-plan request` option's value (`cpPlanMain`'s `value` lambda, cp_verify.cpp:3173-3178): the
/// option may not come twice, and its value must exist.
fn plan_take<'a>(args: &'a [String], into: &mut Option<&'a str>, i: &mut usize) -> bool {
    if into.is_some() || *i + 1 >= args.len() {
        return false;
    }
    *i += 1;
    *into = Some(args[*i].as_str());
    true
}

/// `cpPlanMain()` (`cp_verify.cpp:3120-3218`): the same usage, file reads and rejections as C++.
/// `-plan id` and `-plan accounting` run the stage and print what C++ prints (exit 4). `-plan
/// arrays` (the segment array listing) and `-plan request` are not ported and end NOT CHECKED.
fn plan_main(args: &[String]) -> i32 {
    if args.len() < 3 {
        usage("-plan wants id, request, accounting or arrays");
    }
    let what = args[2].as_str();
    if what == "id" {
        if args.len() != 5 {
            usage("-plan id wants exactly <config folder> <key.bin>");
        }
        let conf = cp_conf_read(&args[3]);
        let key_b = need_bytes(&args[4], "key");
        let policy = PolicyNamed::default();
        let files = StageFiles {
            pol: &conf.pol,
            layout: conf.layout.as_deref(),
            kl: &conf.kl,
            key: &key_b,
            entry: None,
            entry_number: 0,
            request: None,
            y: None,
            odd_statement: false,
            proof: None,
            id_asked: "",
            asked: 0.0,
            quiet: true,
            next_token_asked: false,
            plan_only: true,
            policy: &policy,
        };
        let mut state = StageState::default();
        let out = run_stage(StageMode::PlanId, files, &mut state);
        print!("{}", out.text);
        flush_stdout();
        return out.status;
    }
    if what == "accounting" || what == "arrays" {
        if args.len() != 5 || decimal(&args[4], 1_000_000).is_none() {
            usage(&format!(
                "-plan accounting and -plan arrays want exactly <config folder> <asked>; {}",
                ASKED_FORM
            ));
        }
        if what == "arrays" {
            // The segment array listing (`in.arraysAsked`, vf_segments.inc:163) is not ported.
            return plan_stub();
        }
        let asked = decimal(&args[4], 1_000_000).unwrap() as f64;
        let conf = cp_conf_read(&args[3]);
        // A made-up request: T tokens 0, then r = 0 and e = T. If `lt` is missing or above 20 the
        // request stays empty; the stage rejects such a parameter file.
        let request = match pol_word_u64(&conf.pol, "lt") {
            Some(lt) if lt <= 20 => {
                let mut r = vec![0u32; (1usize << lt) + 2];
                let t = 1u32 << lt;
                *r.last_mut().unwrap() = t;
                r
            }
            _ => Vec::new(),
        };
        let y = vec![0u32];
        let policy = PolicyNamed::default();
        let files = StageFiles {
            pol: &conf.pol,
            layout: conf.layout.as_deref(),
            kl: &conf.kl,
            key: &[],
            entry: None,
            entry_number: 0,
            request: Some(&request),
            y: Some(&y),
            odd_statement: false,
            proof: None,
            id_asked: "",
            asked,
            quiet: true,
            next_token_asked: false,
            plan_only: true,
            policy: &policy,
        };
        let mut state = StageState::default();
        let out = run_stage(StageMode::Request, files, &mut state);
        print!("{}", out.text);
        flush_stdout();
        return out.status;
    }
    if what != "request" {
        usage("-plan wants id, request, accounting or arrays");
    }
    if args.len() < 6 || decimal(&args[5], 1_000_000).is_none() {
        usage(&format!(
            "-plan request wants <policy.txt> <KL.bin> <asked>; {}",
            ASKED_FORM
        ));
    }
    let mut layout_path: Option<&str> = None;
    let mut prompt_path: Option<&str> = None;
    let mut reply_path: Option<&str> = None;
    let mut j_arg: Option<&str> = None;
    let mut i = 6usize;
    while i < args.len() {
        let a = args[i].as_str();
        let mut ok = true;
        if a == "-layout" {
            ok = plan_take(args, &mut layout_path, &mut i);
        } else if a == "-prompt" {
            ok = plan_take(args, &mut prompt_path, &mut i);
        } else if a == "-reply" {
            ok = plan_take(args, &mut reply_path, &mut i);
        } else if a == "-j" {
            ok = plan_take(args, &mut j_arg, &mut i);
        } else if a == "-shapes" || a == "-fields" || a == "-arrays" || a == "-q" {
            // Flags may repeat.
        } else {
            ok = false;
        }
        if !ok {
            usage(&format!(
                "argument {} is not an option of -plan request, comes a second time, or lacks its value",
                i
            ));
        }
        i += 1;
    }
    let mut threads: u32 = 1;
    if let Some(j) = j_arg {
        match decimal(j, 256) {
            Some(v) => threads = v,
            None => usage(THREADS_FORM),
        }
    }
    if threads < 1 || prompt_path.is_none() || reply_path.is_none() {
        usage(&format!("-plan request wants -prompt and -reply; {}", THREADS_FORM));
    }
    let _pol = need_bytes(&args[3], "policy");
    let (_kl, odd) = must_read_words(&args[4], "KL");
    if odd {
        end_with_refusal(Refusal::named("KL-length"), "");
    }
    if let Some(l) = layout_path {
        let _ = need_bytes(l, "layout");
    }
    let _request = must_read_words(prompt_path.unwrap(), "request");
    let _y = must_read_words(reply_path.unwrap(), "y");
    plan_stub()
}

/// The safe ending where a planning mode that is not ported would print its plan.
fn plan_stub() -> i32 {
    let how = "-plan arrays and -plan request are not implemented yet";
    print!("{}", cp_not_checked_lines(how, "internal-stage"));
    flush_stdout();
    5
}

/// `cpUsage()` (`cp_verify.cpp:3015-3115`): the static text, then the fault line, status 2.
fn usage(fault: &str) -> ! {
    eprint!("{}", USAGE);
    eprintln!("cp_verify: this command line was not accepted: {}", fault);
    exit(2)
}

/// Ends a call with a `Refusal`: `NO: <name>` status 1, or `NOT CHECKED: <name>` status 5.
fn end_with_refusal(r: Refusal, how: &str) -> ! {
    match r {
        Refusal::Named(name) => {
            print!("{}", no_line(&name));
            flush_stdout();
            exit(1)
        }
        Refusal::Internal(name) => {
            print!("{}", cp_not_checked_lines(how, &name));
            flush_stdout();
            exit(5)
        }
    }
}

fn flush_stdout() {
    let _ = io::stdout().flush();
}

/// `decimal()` (`vf_common.h:353-365`): 1 to 7 digits, no leading zero, at most `max`.
fn decimal(arg: &str, max: u32) -> Option<u32> {
    let b = arg.as_bytes();
    if b.is_empty() || b.len() > 7 || (b.len() > 1 && b[0] == b'0') {
        return None;
    }
    let mut v = 0u32;
    for &c in b {
        if !c.is_ascii_digit() {
            return None;
        }
        v = 10 * v + (c - b'0') as u32;
    }
    if v > max {
        None
    } else {
        Some(v)
    }
}

/// `cpPolicyHeld()` (`cp_verify.cpp:3254-3273`): compares the caller's policy (or `exact-match`)
/// with the parameter file and the request. A missing or malformed line returns silently; a stage
/// rejects such a file later.
fn cp_policy_held(p: &PolicyNamed, pol: &[u8], request: &[u32]) {
    let (Some(c), Some(theta), Some(cap), Some(s), Some(sh), Some(st)) = (
        pol_word_u64(pol, "C"),
        pol_word_u64(pol, "theta"),
        pol_word_u64(pol, "cap"),
        pol_word_u64(pol, "s"),
        pol_word_u64(pol, "sh"),
        pol_word_u64(pol, "sT"),
    ) else {
        return;
    };
    if st + 4 != sh {
        policy_refused(&format!(
            "the parameter file sets the kind of policy {}; this program takes exact-match and clipped-gap",
            policy_kind(c, theta, cap, s, sh, st)
        ));
    }
    if p.given && !p.is(c, theta, cap, s, sh, st) {
        policy_refused("the option -policy names another kind of policy or another C, theta, cap, s or sh than the parameter file sets");
    }
    let Some(lt) = pol_word_u64(pol, "lt") else { return };
    if lt > 20 || request.len() as u64 != (1u64 << lt) + 2 {
        return;
    }
    let t = 1u64 << lt;
    let r = request[t as usize] as u64;
    let e = request[t as usize + 1] as u64;
    let last = core::cmp::min(e, t - 1);
    if r >= e || e > t {
        return;
    }
    let n = if r < last { last - r } else { 0 };
    if !p.given && n != 0 && !acceptance_policy_is_exact_match(c, theta, cap, sh, st) {
        policy_refused("the request covers more than the output token, the parameter file sets another policy than exact-match, and the call has no -policy");
    }
    policy_says(p, n, t);
}

/// `cpPolicySays()` (`cp_verify.cpp:3241-3252`).
fn policy_says(p: &PolicyNamed, n: u64, t: u64) {
    if !p.given {
        return;
    }
    let kind = policy_empty(n, p.c, p.theta, p.cap, p.sh);
    if kind == 0 {
        return;
    }
    let why = [
        "",
        "C is below 2^sh, the least cost of a token, so no cost is read",
        "theta is below 2^sh, the least cost of a token, so no request can meet it",
        "theta is above C, which no parameter file may set",
        "theta = C and cap is not below the number of the request's tokens that are checked, so none of them is barred",
    ];
    let mut text = format!("a result under the named policy would mean nothing: {}", why[kind as usize]);
    if kind == 4 {
        text.push_str(&format!(
            "; for the output token alone send a request with r = {}",
            t.wrapping_sub(1)
        ));
    }
    policy_refused(&text)
}

/// `cpPolicyRefused()` (`cp_verify.cpp:3235-3238`).
fn policy_refused(why: &str) -> ! {
    print!("policy: {}\nNO: policy\n", why);
    flush_stdout();
    exit(1)
}

/// `CpConf` + `cpConfRead()` (`vf_input_files.h:31-47`). The configuration folder's reads are
/// host-side; the header checks stay in `fp-core`.
struct CpConf {
    pol: Vec<u8>,
    kl: Vec<u32>,
    layout: Option<Vec<u8>>,
}

fn cp_conf_read(folder: &str) -> CpConf {
    let pol = need_bytes(&format!("{}/policy.txt", folder), "policy");
    let (kl, odd) = must_read_words(&format!("{}/KL.bin", folder), "KL");
    if odd {
        end_with_refusal(Refusal::named("KL-length"), "");
    }
    let layout_path = format!("{}/layout.txt", folder);
    // C++ uses lstat(): a name that exists must be readable, even a broken link.
    let has_layout = fs::symlink_metadata(&layout_path).is_ok();
    let layout = if has_layout {
        Some(need_bytes(&layout_path, "layout"))
    } else {
        None
    };
    CpConf { pol, kl, layout }
}

/// Why a read failed: `None` is C++'s `errno == 0` sentence, `Some(e)` is `strerror(e)`.
struct ReadFail(Option<i32>);

/// The checks of `readWholeFile()` (`vf_common.h:145-168`): regular path before the open,
/// regular file after it.
fn read_regular_file(path: &str) -> Result<Vec<u8>, ReadFail> {
    let meta = match fs::metadata(path) {
        Ok(m) => m,
        Err(e) => return Err(ReadFail(e.raw_os_error())),
    };
    if !meta.is_file() {
        return Err(ReadFail(None));
    }
    let mut f = match File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(ReadFail(e.raw_os_error())),
    };
    match f.metadata() {
        Ok(m) if m.is_file() => {}
        Ok(_) => return Err(ReadFail(None)),
        Err(e) => return Err(ReadFail(e.raw_os_error())),
    }
    let mut out = Vec::new();
    match f.read_to_end(&mut out) {
        Ok(_) => Ok(out),
        Err(e) => Err(ReadFail(e.raw_os_error())),
    }
}

/// `needBytes()` (`vf_common.h:317-320`).
fn need_bytes(path: &str, role: &str) -> Vec<u8> {
    match read_regular_file(path) {
        Ok(b) => b,
        Err(ReadFail(errno)) => unreadable(role, errno),
    }
}

/// `readWords()` (`vf_common.h:254-286`), without the parallel reader: words are little-endian,
/// and `odd` says whether the file's length is no multiple of 4.
fn read_words(path: &str) -> Result<(Vec<u32>, bool), ReadFail> {
    let bytes = read_regular_file(path)?;
    let odd = bytes.len() % 4 != 0;
    let words = bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    Ok((words, odd))
}

/// `mustReadWords()` (`vf_common.h:313-316`).
fn must_read_words(path: &str, role: &str) -> (Vec<u32>, bool) {
    match read_words(path) {
        Ok(v) => v,
        Err(ReadFail(errno)) => unreadable(role, errno),
    }
}

/// `unreadableInput()` (`vf_common.h:298-312`): status 2.
fn unreadable(role: &str, errno: Option<i32>) -> ! {
    let why = errno.map(strerror_string);
    print!(
        "{}",
        input_unreadable_line(role, role_name(role), why.as_deref())
    );
    flush_stdout();
    exit(2)
}

// `strerror()` from the host C library, for byte parity with the reference binary.
unsafe extern "C" {
    fn strerror(errnum: i32) -> *const c_char;
}

fn strerror_string(errnum: i32) -> String {
    let p = unsafe { strerror(errnum) };
    if p.is_null() {
        return format!("Unknown error {}", errnum);
    }
    unsafe { CStr::from_ptr(p) }.to_string_lossy().into_owned()
}

/// `cpLengthHeld()` (`cp_verify.cpp:3229-3233`): reject a regular file that is not `4 * words`
/// bytes long, without reading it.
fn cp_length_held(path: &str, words: u64) {
    let Ok(meta) = fs::metadata(path) else {
        return;
    };
    if !meta.is_file() || meta.len() == 4 * words {
        return;
    }
    let name = if meta.len() == 0 || meta.len() % 4 != 0 {
        "statement-required"
    } else {
        "statement-range"
    };
    end_with_refusal(Refusal::named(name), "")
}

// `polWord()` is `fp_core::frame::parameters::pol_word_u64`: the strict parser strips the frame,
// then the named line is read from `Parameters::rest`.
