//! Replay of `scripts/cpp_vectors/common_vectors.cpp`: the verifier-reachable core of
//! `verifier/src/vf_common.h` and the `RoundName` mapping of `vf_transcript_channel.h`.
//!
//! The fixture `fixtures/common_vectors.txt` is the tool's output, byte for byte. Its format is
//! documented at the top of the tool. Refusals that the C++ tool catches through `refuseThrows`
//! are replayed as `Result`/`Option` values.

use std::collections::HashMap;

use fp_core::consts::STATUS_NOT_A_VERIFICATION;
use fp_core::field::ext::{F, E};
use fp_core::field::gl64;
use fp_core::refusal::Refusal;
use fp_core::stage_state::StageState;
use fp_core::verifier::common::{
    above_clip, acceptance_policy_is_exact_match, admit_word, decimal, eq_one, eq_tab, fint,
    fmad1, fmad2, fmad3, good_ending, hex64, internal_name, mix64, order_default, order_range,
    parse_requested_bits, policy_empty, policy_kind, policy_named_read, reject_long_text_file,
    rotary_served, served_form, tau_served, text_number, version_word_admitted, Call, PolicyNamed,
    Served, CE, FIELD_P, FIELD_W, IDHIDDEN, IDLINE, COMMITMENTLINE, LBZ, LBZW,
    NOT_A_VERIFICATION_TEXT, ONE_TIME_LINE_START, RECORDCLAUSE, RESULTWORD, SERVED_EXACT,
    SERVED_LAYOUT, SERVED_NAMED, SERVED_TWO_CODES, STAGEIDLINE, STATUS_STAGE_PASSED_WITH_WORK,
    WITHIN, WITHINSTATUS, WORKLINE, WORK_BITS_MOST, WPE,
};
use fp_core::verifier::transcript::{round_name, RoundName};

const VECTORS: &str = include_str!("../../fixtures/common_vectors.txt");

fn fields(line: &str) -> HashMap<&str, &str> {
    line.split_whitespace()
        .filter_map(|t| t.split_once('='))
        .map(|(k, v)| (k, v))
        .collect()
}

fn num(kv: &HashMap<&str, &str>, k: &str) -> u64 {
    kv.get(k).unwrap_or_else(|| panic!("no field {}", k)).parse().unwrap()
}

fn hexw(s: &str) -> u64 {
    u64::from_str_radix(s, 16).unwrap()
}

fn e(s: &str) -> E {
    let p: Vec<&str> = s.split(',').collect();
    assert_eq!(p.len(), 3, "E {}", s);
    E([F(hexw(p[0])), F(hexw(p[1])), F(hexw(p[2]))])
}

fn zlist(s: &str) -> Vec<E> {
    s.split(';').map(e).collect()
}

fn order(s: &str) -> Vec<u32> {
    if s.is_empty() {
        Vec::new()
    } else {
        s.split(',').map(|x| x.parse().unwrap()).collect()
    }
}

/// The `Served` bit order of the C++ tool (declaration order).
fn served_from_mask(m: u32) -> Served {
    Served {
        experts: m & 1 != 0,
        five_limbs: m & 2 != 0,
        clamps: m & 4 != 0,
        prompt_source: m & 8 != 0,
        placement_table: m & 16 != 0,
        table_digests: m & 32 != 0,
        no_range_words: m & 64 != 0,
        three_bytes: m & 128 != 0,
        ring_degree: m & 256 != 0,
        one_shift: m & 512 != 0,
        one_placement: m & 1024 != 0,
        softmax_table: m & 2048 != 0,
        rotary_table: m & 4096 != 0,
        norm_shifts: m & 8192 != 0,
        two_codes: m & 16384 != 0,
        next_token: m & 32768 != 0,
        exact_match: m & 65536 != 0,
        policy_named: m & 131072 != 0,
    }
}

fn text_constant(key: &str) -> &'static str {
    match key {
        "idline" => IDLINE,
        "stageidline" => STAGEIDLINE,
        "workline" => WORKLINE,
        "resultword" => RESULTWORD,
        "commitmentline" => COMMITMENTLINE,
        "one_time_line_start" => ONE_TIME_LINE_START,
        "recordclause" => RECORDCLAUSE,
        "idhidden" => IDHIDDEN,
        "not_a_verification_text" => NOT_A_VERIFICATION_TEXT,
        "within" => WITHIN,
        "served_layout" => SERVED_LAYOUT,
        "served_two_codes" => SERVED_TWO_CODES,
        "served_exact" => SERVED_EXACT,
        "served_named" => SERVED_NAMED,
        other => panic!("unknown TEXT key {}", other),
    }
}

fn round_name_index(i: usize) -> RoundName {
    match i {
        0 => RoundName::PscEpsilon,
        1 => RoundName::PscRound,
        2 => RoundName::PscY,
        3 => RoundName::Line,
        4 => RoundName::Zero,
        5 => RoundName::BatSigma,
        6 => RoundName::Lkp,
        7 => RoundName::LkpShift,
        8 => RoundName::LkpPlanes,
        9 => RoundName::ForestPoint,
        10 => RoundName::Join,
        11 => RoundName::PscValues,
        _ => panic!("ROUNDNAME index {}", i),
    }
}

#[test]
fn common_vectors_match_the_cpp_reference() {
    let mut at = 0usize;
    let mut text_seen = 0usize;
    let mut tab: Option<(Vec<E>, usize)> = None;
    let mut admit = StageState::default();
    let mut saw_const = false;

    for (lineno, line) in VECTORS.lines().enumerate() {
        at += 1;
        let first = line.split_whitespace().next().unwrap();
        let tag = first.split('=').next().unwrap();
        match tag {
            "CONST" => {
                let kv = fields(line);
                assert_eq!(num(&kv, "ce") as usize, CE);
                assert_eq!(num(&kv, "wpe") as usize, WPE);
                assert_eq!(num(&kv, "le") as i32, fp_core::verifier::common::LE);
                assert_eq!(num(&kv, "lbz") as i32, LBZ);
                assert_eq!(num(&kv, "lbzw") as i32, LBZW);
                assert_eq!(num(&kv, "work_bits_most") as u32, WORK_BITS_MOST);
                assert_eq!(num(&kv, "stage_passed_with_work") as i32, STATUS_STAGE_PASSED_WITH_WORK);
                assert_eq!(num(&kv, "not_a_verification_status") as i32, STATUS_NOT_A_VERIFICATION);
                assert_eq!(num(&kv, "withinstatus") as i32, WITHINSTATUS);
                assert_eq!(hexw(kv["field_p"]), FIELD_P);
                assert_eq!(num(&kv, "field_w"), FIELD_W);
                saw_const = true;
            }
            "TEXT" => {
                let rest = line.strip_prefix("TEXT ").unwrap();
                let (key, value) = rest.split_once('=').unwrap();
                assert_eq!(value, text_constant(key), "TEXT {}", key);
                text_seen += 1;
            }
            "ORDERDEFAULT" => {
                let kv = fields(line);
                assert_eq!(order_default(num(&kv, "mu") as usize), order(kv["o"]));
            }
            "ORDERRANGE" => {
                let kv = fields(line);
                assert_eq!(order_range(num(&kv, "mu") as usize), order(kv["o"]));
            }
            "MIX64" => {
                let kv = fields(line);
                assert_eq!(mix64(hexw(kv["z"])), hexw(kv["m"]), "MIX64 line {}", lineno + 1);
            }
            "TAU" => {
                let kv = fields(line);
                assert_eq!(tau_served(num(&kv, "tau")), kv["ok"] == "1");
            }
            "EXACT" => {
                let kv = fields(line);
                let got = acceptance_policy_is_exact_match(
                    num(&kv, "c"),
                    num(&kv, "theta"),
                    num(&kv, "cap"),
                    num(&kv, "sh"),
                    num(&kv, "st"),
                );
                assert_eq!(got, kv["ok"] == "1");
            }
            "KIND" => {
                let kv = fields(line);
                assert_eq!(
                    policy_kind(
                        num(&kv, "c"),
                        num(&kv, "theta"),
                        num(&kv, "cap"),
                        num(&kv, "s"),
                        num(&kv, "sh"),
                        num(&kv, "st")
                    ),
                    kv["kind"]
                );
            }
            "CLIP" => {
                let kv = fields(line);
                assert_eq!(
                    above_clip(
                        num(&kv, "n"),
                        num(&kv, "c"),
                        num(&kv, "theta"),
                        num(&kv, "cap"),
                        num(&kv, "sh")
                    ),
                    num(&kv, "k")
                );
            }
            "EMPTY" => {
                let kv = fields(line);
                assert_eq!(
                    policy_empty(
                        num(&kv, "n"),
                        num(&kv, "c"),
                        num(&kv, "theta"),
                        num(&kv, "cap"),
                        num(&kv, "sh")
                    ) as u64,
                    num(&kv, "e")
                );
            }
            "ROTARY" => {
                let kv = fields(line);
                assert_eq!(rotary_served(num(&kv, "theta0"), num(&kv, "dh"), num(&kv, "lt")), kv["ok"] == "1");
            }
            "GOOD" => {
                let kv = fields(line);
                assert_eq!(good_ending(kv["below"] == "1", kv["notserved"] == "1"), kv["ok"] == "1");
            }
            "VERSION" => {
                let kv = fields(line);
                assert_eq!(
                    version_word_admitted(u32::from_str_radix(kv["v"], 16).unwrap()),
                    kv["ok"] == "1"
                );
            }
            "ADMIT" => {
                let kv = fields(line);
                let v = u32::from_str_radix(kv["v"], 16).unwrap();
                assert_eq!(admit_word(&mut admit, v), kv["ok"] == "1", "ADMIT line {}", lineno + 1);
                assert_eq!(admit.run_version_word_fixed, kv["fixed"] == "1");
                assert_eq!(
                    admit.run_version_word,
                    u32::from_str_radix(kv["run"], 16).unwrap()
                );
            }
            "LONGFILE" => {
                let kv = fields(line);
                let got = reject_long_text_file(num(&kv, "bytes"));
                match got {
                    Ok(()) => assert_eq!(kv["result"], "ok"),
                    Err(r) => assert_eq!(r.name(), kv["result"]),
                }
            }
            "INTERNAL" => {
                let kv = fields(line);
                assert_eq!(internal_name(kv["name"]), kv["ok"] == "1");
            }
            "HEX64" => {
                let kv = fields(line);
                let words: Vec<u32> = kv["in"].split(',').map(|x| u32::from_str_radix(x, 16).unwrap()).collect();
                assert_eq!(hex64(&words), kv["out"]);
            }
            "FINT" => {
                let kv = fields(line);
                let v: i64 = kv["v"].parse().unwrap();
                assert_eq!(fint(v), hexw(kv["r"]));
            }
            "FMAD1" => {
                let kv = fields(line);
                assert_eq!(
                    fmad1(num(&kv, "a"), num(&kv, "x"), num(&kv, "y")),
                    hexw(kv["r"])
                );
            }
            "FMAD2" => {
                let kv = fields(line);
                assert_eq!(
                    fmad2(
                        num(&kv, "a"),
                        num(&kv, "x1"),
                        num(&kv, "y1"),
                        num(&kv, "x2"),
                        num(&kv, "y2")
                    ),
                    hexw(kv["r"])
                );
            }
            "FMAD3" => {
                let kv = fields(line);
                assert_eq!(
                    fmad3(
                        num(&kv, "a"),
                        num(&kv, "x1"),
                        num(&kv, "y1"),
                        num(&kv, "x2"),
                        num(&kv, "y2"),
                        num(&kv, "x3"),
                        num(&kv, "y3")
                    ),
                    hexw(kv["r"])
                );
            }
            "DEC" => {
                let kv = fields(line);
                let got = decimal(kv["arg"], 1_000_000);
                assert_eq!(got.map(|x| x as u64), if kv["ok"] == "1" { Some(num(&kv, "v")) } else { None });
            }
            "PARSEBITS" => {
                let kv = fields(line);
                let got = parse_requested_bits(kv["arg"]);
                assert_eq!(
                    got.map(|x| x as u64),
                    if kv["ok"] == "1" { Some(num(&kv, "v")) } else { None }
                );
            }
            "EQTAB" => {
                let kv = fields(line);
                let z = zlist(kv["z"]);
                let len: usize = kv["len"].parse().unwrap();
                let off: usize = kv["off"].parse().unwrap();
                let count: usize = kv["count"].parse().unwrap();
                let got = eq_tab(&z[off..off + len], len);
                assert_eq!(got.len(), count, "EQTAB count line {}", lineno + 1);
                tab = Some((got, 0));
            }
            "EQTABV" => {
                let kv = fields(line);
                let i: usize = kv["i"].parse().unwrap();
                let (got, next) = tab.as_mut().unwrap();
                assert_eq!(*next, i, "EQTABV order");
                assert_eq!(e(kv["v"]), got[i], "EQTABV line {}", lineno + 1);
                *next += 1;
                let done = *next == got.len();
                if done {
                    tab = None;
                }
            }
            "EQONE" => {
                let kv = fields(line);
                let z = zlist(kv["z"]);
                let len: i32 = kv["len"].parse().unwrap();
                let off: usize = kv["off"].parse().unwrap();
                let c = num(&kv, "c");
                assert_eq!(eq_one(&z[off..], len, c).unwrap(), e(kv["v"]), "EQONE line {}", lineno + 1);
            }
            "EQONEERR" => {
                let kv = fields(line);
                let len: i32 = kv["len"].parse().unwrap();
                let c = num(&kv, "c");
                let z = vec![E::one(); 64];
                assert_eq!(
                    eq_one(&z, len, c),
                    Err(Refusal::internal("internal-eq-index")),
                    "EQONEERR line {}",
                    lineno + 1
                );
                assert_eq!(kv["result"], "internal-eq-index");
            }
            "POLICYREAD" => {
                let kv = fields(line);
                let got: Option<PolicyNamed> = policy_named_read(kv["text"]);
                assert_eq!(got.is_some(), kv["ok"] == "1", "POLICYREAD {}", kv["text"]);
                if let Some(p) = got {
                    assert!(p.given);
                    assert_eq!(p.kind, kv["kind"]);
                    assert_eq!(p.c, num(&kv, "c"));
                    assert_eq!(p.theta, num(&kv, "theta"));
                    assert_eq!(p.cap, num(&kv, "cap"));
                    assert_eq!(p.s, num(&kv, "s"));
                    assert_eq!(p.sh, num(&kv, "sh"));
                }
            }
            "SERVED" => {
                let rest = line.split_once(" form=").unwrap().1;
                let mask = u32::from_str_radix(line.split_whitespace().nth(1).unwrap().split_once('=').unwrap().1, 16)
                    .unwrap();
                assert_eq!(served_form(&served_from_mask(mask)), rest, "SERVED mask {:05x}", mask);
            }
            "ROUNDNAME" => {
                let rest = line.strip_prefix("ROUNDNAME i=").unwrap();
                let (i, name) = rest.split_once(" name=").unwrap();
                let i: usize = i.parse().unwrap();
                assert_eq!(round_name(round_name_index(i)), name);
            }
            other => panic!("line {}: unknown tag {}", lineno + 1, other),
        }
    }

    assert!(saw_const && text_seen == 14, "the fixture has its CONST and 14 TEXT records");
    assert_eq!(at, VECTORS.lines().count());
    assert!(tab.is_none(), "the last EQTAB is complete");

    // The command-line helpers agree with the constants they quote.
    assert_eq!(text_number(fp_core::consts::THRESHOLD_BITS_TEXT), fp_core::consts::BAR as u32);

    // `Call`'s C++ accessors.
    let mut c = Call::default();
    c.kappa = 5;
    c.iota = 2;
    c.t0 = 10;
    assert_eq!(c.k_count(), 32);
    assert_eq!(c.i_count(), 4);
    assert_eq!(c.tau_at(7), 7, "no tau vector: the row itself");
    c.tau = Some(vec![3, 1, 4]);
    assert_eq!(c.tau_at(2), 4);
    assert_eq!(gl64::P, FIELD_P);
}
