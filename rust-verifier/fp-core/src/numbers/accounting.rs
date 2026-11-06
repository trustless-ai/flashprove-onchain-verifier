//! The plan's error accounting, ported from `blocks/numbers/accounting.h`.
//!
//! `account()` computes the numbers from a finished plan alone. The printed figures are the
//! program's own estimate, not a security level. This port keeps the exact comparisons and the
//! `f64` figures for printing (`bits_of`, `cut2`).

use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;

use super::plan::{Cause, PlanRound, Planned, Priced};
use super::real::{bits_of, cut2, Dir, Real};
use super::setting::{CountSource, ErrorKind, RoundKind};

/// Rounds with the same name, work and printed error (`AccountGroup`).
#[derive(Clone, Debug)]
pub struct AccountGroup {
    pub bits: f64,
    pub work: u32,
    pub rounds: u64,
    pub name: String,
    pub holds: bool,
    pub list: bool,
}

impl Default for AccountGroup {
    fn default() -> Self {
        AccountGroup { bits: 0.0, work: 0, rounds: 0, name: String::new(), holds: true, list: false }
    }
}

impl AccountGroup {
    pub fn all(&self) -> f64 {
        self.bits + self.work as f64
    }
}

/// What `account()` returns (`Accounting`).
#[derive(Clone, Debug)]
pub struct Accounting {
    pub formed: bool,
    pub holds: bool,
    pub needs_work: bool,
    pub refused: String,
    pub why_not: String,
    pub target: u32,
    pub digest_bits: u32,
    pub rounds: u64,
    pub queries: u64,
    pub groups: Vec<AccountGroup>,
    pub worst: String,
    pub lists: AccountGroup,
    pub sum: f64,
    pub sum_lists: f64,
    pub planned_calls: u64,
    pub counted: bool,
    pub calls: u64,
    pub work: [[u32; 3]; 6],
    pub closeness: [u64; 2],
    pub circle: bool,
    pub small_union: AccountGroup,
    pub small_columns: u64,
    pub near: u64,
    pub near_small: u64,
    pub near_closeness: [u64; 2],
    pub by_work: u64,
    pub on_a_word: u64,
}

impl Default for Accounting {
    fn default() -> Self {
        Accounting {
            formed: false,
            holds: false,
            needs_work: false,
            refused: String::new(),
            why_not: String::new(),
            target: 0,
            digest_bits: 256,
            rounds: 0,
            queries: 0,
            groups: Vec::new(),
            worst: String::new(),
            lists: AccountGroup::default(),
            sum: 0.0,
            sum_lists: 0.0,
            planned_calls: 0,
            counted: false,
            calls: 0,
            work: [[0; 3]; 6],
            closeness: [0; 2],
            circle: false,
            small_union: AccountGroup::default(),
            small_columns: 0,
            near: 0,
            near_small: 0,
            near_closeness: [0; 2],
            by_work: 0,
            on_a_word: 0,
        }
    }
}

impl Accounting {
    pub fn any_work(&self) -> bool {
        for i in 0..5 {
            if self.work[i][0] != 0 || self.work[i][1] != 0 || self.work[i][2] != 0 {
                return true;
            }
        }
        false
    }
}

fn rests_index(c: CountSource) -> usize {
    match c {
        CountSource::Third => 0,
        CountSource::Johnson => 1,
    }
}

/// Runs of digits become one `#` (`digits_as_hash`).
pub fn digits_as_hash(s: &str) -> String {
    let mut o = String::new();
    for c in s.chars() {
        if c.is_ascii_digit() {
            if !o.ends_with('#') {
                o.push('#');
            }
        } else {
            o.push(c);
        }
    }
    o
}

fn group_name(r: &PlanRound) -> String {
    if r.where_.is_empty() {
        r.name.clone()
    } else {
        alloc::format!("{} ({})", r.name, r.where_)
    }
}

/// Forms the accounting of one part (`account`). `part < 0` means the whole plan.
pub fn account(p: &Planned, part: i32) -> Accounting {
    let mut a = Accounting::default();
    if p.cause() == Cause::Refused {
        a.refused = String::from(p.why_not());
    }
    a.target = p.set.target;
    a.digest_bits = 8 * p.set.digest_bytes;
    a.circle = p.set.circle;
    let mut worst: Option<usize> = None;
    for i in 0..6 {
        for j in 0..3 {
            a.work[i][j] = p.set.work[i][j];
        }
    }
    let mut sum = Real::default();
    let mut sum_lists = Real::default();
    a.holds = p.cause() != Cause::Refused;
    let block = p.set.hash_block_bytes as u64;
    let unit = p.capped();
    for (idx, r) in p.rounds.iter().enumerate() {
        if part >= 0 && r.part as i32 != part {
            continue;
        }
        if r.word_fault().is_some() {
            a.holds = false;
        }
        if r.priced == Priced::OnTheCallersWord {
            a.on_a_word += r.count;
        }
        a.rounds += r.count;
        if r.kind != RoundKind::Empty {
            a.queries += r.count;
        }
        let words = r.draw_e * p.set.degree as u64 + r.draw_positions + (r.draw_trits + 31) / 32;
        let free = if r.work_bits != 0 { 0 } else { p.set.chain_free_words as u64 };
        a.planned_calls += r.count
            * ((r.message_bytes as u64 + p.set.chain_extra_bytes as u64 + block - 1) / block
                + if words > free { (words - free + 7) / 8 } else { 0 });
        let error = p.whole_error(r, &unit);
        if error.zero() {
            continue;
        }
        if !p.holds_round(r, &unit) {
            a.holds = false;
        }
        if Real::cmp(&error, &Real::two_to(-(p.set.target as i64))) == Ordering::Greater {
            a.needs_work = true;
            a.by_work += r.count;
        }
        if p.holds_round(r, &unit) && bits_of(&error) + (r.work_bits as f64) < p.set.target as f64 + 0.01 {
            a.near += r.count;
            if r.why == ErrorKind::Small {
                a.near_small += r.count;
            }
            if r.why == ErrorKind::Closeness {
                a.near_closeness[rests_index(r.rests)] += r.count;
            }
        }
        if r.why == ErrorKind::Closeness {
            a.closeness[rests_index(r.rests)] += r.count;
        }
        if r.draw_trits != 0 {
            let n = r.combinations;
            let columns = if n != 0 { r.draw_trits / n } else { 0 };
            let columns_real = Real::from_u64(columns);
            let bits = bits_of(&Real::mul(&error, &columns_real, Dir::Up));
            if columns != 0
                && (a.small_columns == 0 || bits + (r.work_bits as f64) < a.small_union.all())
            {
                a.small_columns = columns;
                a.small_union.bits = bits;
                a.small_union.work = r.work_bits;
                a.small_union.rounds = r.count;
                a.small_union.name = group_name(r);
            }
        }
        let worse = match worst {
            None => true,
            Some(w) => {
                let ew = p.whole_error(&p.rounds[w], &unit);
                let a1 = Real::mul(&ew, &Real::two_to(-(p.rounds[w].work_bits as i64)), Dir::Up);
                let a2 = Real::mul(&error, &Real::two_to(-(r.work_bits as i64)), Dir::Up);
                Real::cmp(&a1, &a2) == Ordering::Less
            }
        };
        if worse {
            worst = Some(idx);
        }
        let all = Real::mul(&error, &Real::from_u64(r.count), Dir::Up);
        sum_lists = Real::add(&sum_lists, &all, Dir::Up);
        sum = Real::add(
            &sum,
            &Real::mul(&all, &Real::two_to(-(r.work_bits as i64)), Dir::Up),
            Dir::Up,
        );
        let mut g = AccountGroup::default();
        g.bits = bits_of(&error);
        g.work = r.work_bits;
        g.rounds = r.count;
        g.holds = p.holds_round(r, &unit);
        g.list = r.why == ErrorKind::Query;
        g.name = digits_as_hash(&group_name(r));
        a.groups.push(g);
    }
    for m in &p.messages {
        if part < 0 || m.part as i32 == part {
            a.planned_calls += m.hash_calls * m.count;
        }
    }
    if !a.holds {
        a.why_not = String::from(p.why_not());
    }
    if a.groups.is_empty() {
        return a;
    }
    a.groups.sort_by(|x, y| {
        let c = x.name.cmp(&y.name);
        if c != Ordering::Equal {
            return c;
        }
        let c = x.work.cmp(&y.work);
        if c != Ordering::Equal {
            return c;
        }
        x.bits.partial_cmp(&y.bits).unwrap_or(Ordering::Equal)
    });
    let mut o: Vec<AccountGroup> = Vec::new();
    for x in a.groups.drain(..) {
        if let Some(last) = o.last_mut() {
            if last.name == x.name && last.work == x.work && cut2(last.bits) == cut2(x.bits) {
                last.rounds += x.rounds;
                last.holds = last.holds && x.holds;
                continue;
            }
        }
        o.push(x);
    }
    a.groups = o;
    a.groups.sort_by(|x, y| {
        let c = x.all().partial_cmp(&y.all()).unwrap_or(Ordering::Equal);
        if c != Ordering::Equal {
            c
        } else {
            x.name.cmp(&y.name)
        }
    });
    a.lists = a.groups[0].clone();
    for x in &a.groups {
        if x.bits < a.lists.bits {
            a.lists = x.clone();
        }
    }
    a.sum = bits_of(&sum);
    a.sum_lists = bits_of(&sum_lists);
    if let Some(w) = worst {
        a.worst = group_name(&p.rounds[w]);
    }
    a.formed = true;
    a
}

/// `compiled_level`: the compiled bound as one number (`accounting.h`).
pub fn compiled_level(w: f64, digest_bits: u32) -> f64 {
    let mut lo = 0.0f64;
    let mut hi = digest_bits as f64 - 1.0;
    for _ in 0..200 {
        let l = (lo + hi) / 2.0;
        if libm::pow(2.0, -l)
            >= libm::pow(2.0, -w) + 8.5 * libm::pow(2.0, l - digest_bits as f64)
        {
            lo = l;
        } else {
            hi = l;
        }
    }
    lo
}
