//! Lane C golden gate: parse the C++ plan dump, rebuild every round/message in Rust, run Rust's
//! `account()`, and match the C++ accounting field by field. The four numbers of `result-v1` must
//! come out of the Rust computation: least-round=128.00, least-round-without-work=96.23,
//! work-rounds=38, commitment-assumed-rounds=49.

use fp_core::numbers::accounting::{account, Accounting};
use fp_core::numbers::plan::{
    MessageKind, PlanMessage, PlanRound, Planned, Priced, PricedCode, PricedGroup, PricedTable,
    TableDistances, TableTest,
};
use fp_core::numbers::real::{cut2, Big, Real};
use fp_core::numbers::setting::{
    CountSource, ErrorKind, RoundKind, Scope, Setting,
};

const DUMP: &str = include_str!("../../fixtures/plans_dump.txt");

fn big(s: &str) -> Big {
    if s == "0" || s.is_empty() {
        Big::zero()
    } else {
        Big {
            w: s
                .split(',')
                .map(|x| u32::from_str_radix(x, 16).unwrap())
                .collect(),
        }
    }
}

fn real(s: &str) -> Real {
    let (m, e) = s.split_once('@').unwrap();
    Real { m: big(m), e: e.parse().unwrap() }
}

fn bool_of(s: &str) -> bool {
    s == "1"
}

fn parse_setting(t: &[&str]) -> Setting {
    assert_eq!(t[0], "SETTING");
    assert_eq!(t.len(), 37, "SETTING fields");
    let mut work = [[0u32; 3]; 6];
    for i in 0..6 {
        for j in 0..3 {
            work[i][j] = t[19 + 3 * i + j].parse().unwrap();
        }
    }
    let mut s = Setting::default();
    s.field_name = t[1].to_string();
    s.p = big(t[2]);
    s.degree = t[3].parse().unwrap();
    s.circle = bool_of(t[4]);
    s.f_bytes = t[5].parse().unwrap();
    s.e_bytes = t[6].parse().unwrap();
    s.digest_bytes = t[7].parse().unwrap();
    s.salt_bytes = t[8].parse().unwrap();
    s.nonce_bytes = t[9].parse().unwrap();
    s.position_bytes = t[10].parse().unwrap();
    s.hash_block_bytes = t[11].parse().unwrap();
    s.label_bytes = t[12].parse().unwrap();
    s.chain_extra_bytes = t[13].parse().unwrap();
    s.chain_free_words = t[14].parse().unwrap();
    s.target = t[15].parse().unwrap();
    s.instances = t[16].parse().unwrap();
    s.samples = t[17].parse().unwrap();
    s.saved_coefficient = bool_of(t[18]);
    s.work = work;
    s
}

fn kind_of(x: u32) -> RoundKind {
    match x {
        0 => RoundKind::Empty,
        1 => RoundKind::Algebraic,
        2 => RoundKind::Epsilon,
        3 => RoundKind::Seed,
        4 => RoundKind::Positions,
        5 => RoundKind::Bits,
        6 => RoundKind::Seal,
        7 => RoundKind::Record,
        _ => panic!("kind {}", x),
    }
}

fn why_of(x: u32) -> ErrorKind {
    match x {
        0 => ErrorKind::Field,
        1 => ErrorKind::Sample,
        2 => ErrorKind::Closeness,
        3 => ErrorKind::Query,
        4 => ErrorKind::Small,
        5 => ErrorKind::Zero,
        _ => panic!("why {}", x),
    }
}

fn scope_of(x: u32) -> Scope {
    match x {
        0 => Scope::Request,
        1 => Scope::Shared,
        2 => Scope::Once,
        _ => panic!("scope {}", x),
    }
}

fn rests_of(x: u32) -> CountSource {
    match x {
        0 => CountSource::Third,
        1 => CountSource::Johnson,
        _ => panic!("rests {}", x),
    }
}

fn priced_of(x: u32) -> Priced {
    match x {
        0 => Priced::Nothing,
        1 => Priced::SettingAlone,
        2 => Priced::TheRoundItself,
        3 => Priced::AsSaid,
        4 => Priced::OnTheCallersWord,
        _ => panic!("priced {}", x),
    }
}

fn test_of(x: u32) -> TableTest {
    match x {
        0 => TableTest::Later,
        1 => TableTest::OneTime,
        2 => TableTest::Link,
        _ => panic!("table test {}", x),
    }
}

fn parse_round(t: &[&str]) -> PlanRound {
    assert_eq!(t[0], "ROUND");
    assert_eq!(t.len(), 47, "ROUND fields");
    let mut r = PlanRound::default();
    r.name = t[1].to_string();
    r.where_ = t[2].to_string();
    r.kind = kind_of(t[3].parse().unwrap());
    r.why = why_of(t[4].parse().unwrap());
    r.scope = scope_of(t[5].parse().unwrap());
    r.error = real(t[6]);
    r.rests = rests_of(t[7].parse().unwrap());
    r.work_bits = t[8].parse().unwrap();
    r.count = t[9].parse().unwrap();
    r.part = t[10].parse().unwrap();
    r.message_bytes = t[11].parse().unwrap();
    r.roots = t[12].parse().unwrap();
    r.answers = t[13].parse().unwrap();
    r.draw_e = t[14].parse().unwrap();
    r.draw_nonzero = t[15].parse().unwrap();
    r.draw_positions = t[16].parse().unwrap();
    r.log_n = t[17].parse().unwrap();
    r.draw_trits = t[18].parse().unwrap();
    r.rows = t[19].parse().unwrap();
    r.first_list = t[20].parse().unwrap();
    r.combinations = t[21].parse().unwrap();
    r.sharing = t[22].parse().unwrap();
    r.priced = priced_of(t[23].parse().unwrap());
    r.group = PricedGroup {
        main: PricedCode {
            log_n: t[24].parse().unwrap(),
            ell: t[25].parse().unwrap(),
            r: t[26].parse().unwrap(),
        },
        mask: PricedCode {
            log_n: t[27].parse().unwrap(),
            ell: t[28].parse().unwrap(),
            r: t[29].parse().unwrap(),
        },
        k: t[30].parse().unwrap(),
        h: t[31].parse().unwrap(),
        slots: t[32].parse().unwrap(),
        said: bool_of(t[33]),
        rule: t[34].parse().unwrap(),
        m: t[35].parse().unwrap(),
    };
    r.table = PricedTable {
        code: PricedCode {
            log_n: t[36].parse().unwrap(),
            ell: t[37].parse().unwrap(),
            r: t[38].parse().unwrap(),
        },
        v: t[39].parse().unwrap(),
        answers: t[40].parse().unwrap(),
        distances: TableDistances {
            radius: t[41].parse().unwrap(),
            later_radius: t[42].parse().unwrap(),
            m_once: t[43].parse().unwrap(),
            m_later: t[44].parse().unwrap(),
        },
        said: bool_of(t[45]),
        test: test_of(t[46].parse().unwrap()),
    };
    r
}

fn parse_message(t: &[&str]) -> PlanMessage {
    assert_eq!(t[0], "MESSAGE");
    assert_eq!(t.len(), 9, "MESSAGE fields");
    PlanMessage {
        name: t[1].to_string(),
        where_: t[2].to_string(),
        kind: match t[3].parse().unwrap() {
            0 => MessageKind::Scalars,
            1 => MessageKind::Answers,
            2 => MessageKind::Root,
            3 => MessageKind::Nonce,
            4 => MessageKind::Columns,
            5 => MessageKind::Salts,
            6 => MessageKind::Paths,
            7 => MessageKind::Head,
            x => panic!("message kind {}", x),
        },
        bytes: t[4].parse().unwrap(),
        expected: t[5].parse().unwrap(),
        count: t[6].parse().unwrap(),
        part: t[7].parse().unwrap(),
        in_chain: bool_of(t[8]),
        hash_calls: 0,
    }
}

// MESSAGE has 10 fields in the dump; fix the reader above to match it.
fn parse_message10(t: &[&str]) -> PlanMessage {
    assert_eq!(t.len(), 10, "MESSAGE fields");
    let mut m = parse_message(&t[..9]);
    m.hash_calls = t[9].parse().unwrap();
    m
}

#[derive(Debug)]
struct AccountDump {
    formed: bool,
    holds: bool,
    needs_work: bool,
    target: u32,
    digest_bits: u32,
    rounds: u64,
    queries: u64,
    groups: usize,
    g0_bits: f64,
    g0_work: u32,
    g0_rounds: u64,
    g0_name: String,
    g0_holds: bool,
    g0_list: bool,
    lists_bits: f64,
    lists_work: u32,
    closeness: [u64; 2],
    by_work: u64,
    near: u64,
    near_small: u64,
    near_closeness: [u64; 2],
    sum: f64,
    sum_lists: f64,
    planned_calls: u64,
    small_columns: u64,
    small_union_all: f64,
    small_union_work: u32,
    on_a_word: u64,
}

fn parse_account(t: &[&str]) -> AccountDump {
    assert_eq!(t[0], "ACCOUNT");
    assert_eq!(t.len(), 32, "ACCOUNT fields");
    AccountDump {
        formed: bool_of(t[2]),
        holds: bool_of(t[3]),
        needs_work: bool_of(t[4]),
        target: t[5].parse().unwrap(),
        digest_bits: t[6].parse().unwrap(),
        rounds: t[7].parse().unwrap(),
        queries: t[8].parse().unwrap(),
        groups: t[9].parse().unwrap(),
        g0_bits: t[10].parse().unwrap(),
        g0_work: t[11].parse().unwrap(),
        g0_rounds: t[12].parse().unwrap(),
        g0_name: t[13].to_string(),
        g0_holds: bool_of(t[14]),
        g0_list: bool_of(t[15]),
        lists_bits: t[16].parse().unwrap(),
        lists_work: t[17].parse().unwrap(),
        closeness: [t[18].parse().unwrap(), t[19].parse().unwrap()],
        by_work: t[20].parse().unwrap(),
        near: t[21].parse().unwrap(),
        near_small: t[22].parse().unwrap(),
        near_closeness: [t[23].parse().unwrap(), t[24].parse().unwrap()],
        sum: t[25].parse().unwrap(),
        sum_lists: t[26].parse().unwrap(),
        planned_calls: t[27].parse().unwrap(),
        small_columns: t[28].parse().unwrap(),
        small_union_all: t[29].parse().unwrap(),
        small_union_work: t[30].parse().unwrap(),
        on_a_word: t[31].parse().unwrap(),
    }
}

fn close(a: f64, b: f64) -> bool {
    cut2(a) == cut2(b)
}

#[test]
fn cpp_plan_dump_matches_rust_accounting() {
    let mut set: Option<Setting> = None;
    let mut current: Option<(String, Vec<PlanRound>, Vec<PlanMessage>, Vec<String>)> = None;
    let mut plans: Vec<(String, Planned, AccountDump)> = Vec::new();
    for (lineno, line) in DUMP.lines().enumerate() {
        let t: Vec<&str> = line.split('\t').collect();
        match t[0] {
            "SETTING" => set = Some(parse_setting(&t)),
            "PLAN" => {
                assert_eq!(t.len(), 3, "PLAN line {}", lineno + 1);
                current = Some((t[1].to_string(), Vec::new(), Vec::new(), Vec::new()));
            }
            "PART" => current.as_mut().unwrap().3.push(t[1].to_string()),
            "ROUND" => current.as_mut().unwrap().1.push(parse_round(&t)),
            "MESSAGE" => current.as_mut().unwrap().2.push(parse_message10(&t)),
            "ACCOUNT" => {
                let a = parse_account(&t);
                let (name, rounds, messages, parts) = current.take().unwrap();
                let p = Planned::new(set.clone().unwrap(), rounds, messages, parts, String::new());
                plans.push((name, p, a));
            }
            other => panic!("unknown dump line {} at {}", other, lineno + 1),
        }
    }
    assert_eq!(plans.len(), 4);
    assert_eq!(
        plans.iter().map(|p| p.0.as_str()).collect::<Vec<_>>(),
        ["key", "entry", "proof", "all"]
    );

    for (name, p, want) in &plans {
        let got: Accounting = account(p, -1);
        assert_eq!(got.formed, want.formed, "{} formed", name);
        assert_eq!(got.holds, want.holds, "{} holds", name);
        assert_eq!(got.needs_work, want.needs_work, "{} needs_work", name);
        assert_eq!(got.target, want.target, "{} target", name);
        assert_eq!(got.digest_bits, want.digest_bits, "{} digest_bits", name);
        assert_eq!(got.rounds, want.rounds, "{} rounds", name);
        assert_eq!(got.queries, want.queries, "{} queries", name);
        assert_eq!(got.groups.len(), want.groups, "{} group count", name);
        let g0 = &got.groups[0];
        assert!(close(g0.bits, want.g0_bits), "{} g0 bits {} vs {}", name, g0.bits, want.g0_bits);
        assert_eq!(g0.work, want.g0_work, "{} g0 work", name);
        assert_eq!(g0.rounds, want.g0_rounds, "{} g0 rounds", name);
        assert_eq!(g0.name, want.g0_name, "{} g0 name", name);
        assert_eq!(g0.holds, want.g0_holds, "{} g0 holds", name);
        assert_eq!(g0.list, want.g0_list, "{} g0 list", name);
        assert!(close(got.lists.bits, want.lists_bits), "{} lists bits", name);
        assert_eq!(got.lists.work, want.lists_work, "{} lists work", name);
        assert_eq!(got.closeness, want.closeness, "{} closeness", name);
        assert_eq!(got.by_work, want.by_work, "{} by_work", name);
        assert_eq!(got.near, want.near, "{} near", name);
        assert_eq!(got.near_small, want.near_small, "{} near_small", name);
        assert_eq!(got.near_closeness, want.near_closeness, "{} near_closeness", name);
        assert!(close(got.sum, want.sum), "{} sum", name);
        assert!(close(got.sum_lists, want.sum_lists), "{} sum_lists", name);
        assert_eq!(got.planned_calls, want.planned_calls, "{} planned_calls", name);
        assert_eq!(got.small_columns, want.small_columns, "{} small_columns", name);
        assert!(
            close(got.small_union.all(), want.small_union_all),
            "{} small_union",
            name
        );
        assert_eq!(got.small_union.work, want.small_union_work, "{} small_union work", name);
        assert_eq!(got.on_a_word, want.on_a_word, "{} on_a_word", name);
    }

    let all = account(&plans[3].1, -1);
    let key = account(&plans[0].1, -1);
    let entry = account(&plans[1].1, -1);
    assert_eq!(cut2(all.groups[0].all()), 128.00);
    assert_eq!(cut2(all.lists.bits), 96.23);
    assert_eq!(all.by_work, 38);
    assert_eq!(key.closeness[1] + entry.closeness[1], 49);
}
