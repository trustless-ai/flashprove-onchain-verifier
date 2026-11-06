//! What a planning call prints (`blocks/frame/prints.h`): the sizes of the groups, the columns
//! drawn, each file's length and what its proximity terms rest on. The listings of rounds and
//! fields (`print_rounds`, `print_fields`) are not ported: the planning cases print neither.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::frame::files::{file_entry, file_key, file_proof, merged, FilePlan, Sized, Subproofs};
use crate::numbers::accounting::account;
use crate::numbers::accounting_print::print_accounting;
use crate::frame::derive::TestSizes;
use crate::numbers::blocks::{analysis_group, rng_combinations, weakest_source};
use crate::numbers::codes::{name_of_radius, rests_on};
use crate::numbers::setting::{Scope, Setting};

/// `print_test()` (`prints.h:21-38`).
pub fn print_test(out: &mut String, s: &Setting, name: &str, x: &TestSizes) {
    let g = &x.group;
    let a = analysis_group(s, g);
    out.push_str(&format!(
        "group: {}: code 2^{}, message {} + {} random, 2^{} rows; mask code 2^{}, {} + {}; distance {:.6}, ",
        name,
        g.main.log_n,
        g.main.ell,
        g.main.r,
        g.k,
        g.mask.log_n,
        g.mask.ell,
        g.mask.r,
        a.at.delta.lo.value()
    ));
    if g.m != 0 {
        out.push_str(&format!("m = {}, ", g.m));
    }
    out.push_str(&format!(
        "list {}, {} positions; rule: {}; its closeness terms rest on {}\n",
        a.list.dec(),
        x.t,
        name_of_radius(g.rule),
        rests_on(weakest_source(&a))
    ));
    for i in 1..x.stages.len() {
        let sg = &x.stages[i].g;
        out.push_str(&format!(
            "group:   stage {}: 2^{} rows of {} + {} in 2^{}; 2^{} mask rows of {} + {} in 2^{}; list {}, {} positions\n",
            i + 1,
            sg.k,
            sg.main.ell,
            sg.main.r,
            sg.main.log_n,
            sg.h,
            sg.mask.ell,
            sg.mask.r,
            sg.mask.log_n,
            analysis_group(s, sg).list.dec(),
            x.stages[i].t
        ));
    }
}

/// `print_size()` (`prints.h:41-46`).
pub fn print_size(out: &mut String, p: &crate::numbers::plan::Planned, part: &str) {
    let Some(i) = p.part_index(part) else { return };
    let (bytes, expected) = p.size_of(i as u32);
    out.push_str(&format!(
        "length: {}: at most {} bytes, {:.0} on average over the drawn positions\n",
        part, bytes, expected
    ));
}

/// `print_plan()` (`prints.h:48-92`), with the round and field listings left out.
pub fn print_plan(
    out: &mut String,
    what: &str,
    z: &Sized,
    sub: &Subproofs,
    rounds: bool,
    fields: bool,
) -> bool {
    assert!(!rounds && !fields, "print_plan: the round and field listings are not ported");
    let d = &z.d;
    let mut last = 0u64;
    let mut files: Vec<FilePlan> = Vec::new();
    if what == "key" || what == "request" {
        files.push(file_key(z, true, &mut last));
    }
    if what == "leaf" || what == "request" {
        files.push(file_entry(z, true, &mut last));
    }
    if what == "request" {
        files.push(file_proof(z, sub, true, &mut last));
    }
    let p = merged(&d.set, &files);
    if what == "request" {
        print_test(out, &d.set, "link", &d.link);
        print_test(out, &d.set, "last test", &d.last);
    }
    for (batch, x) in [(true, &z.batch), (false, &z.once)] {
        if what == "leaf" || (what == "key" && batch) {
            continue;
        }
        out.push_str(if batch {
            "group: in a batch:\n"
        } else {
            "group: in the committer's files:\n"
        });
        print_test(out, &d.set, "folded table", &x.folded);
        if x.s.shared_split_needed() {
            print_test(out, &d.set, "Omega", &x.omega);
        }
        print_test(out, &d.set, "own test", &x.own);
        if !batch {
            print_test(out, &d.set, "ranges' multiplicities", &z.ranges.test);
        }
    }
    if what != "key" {
        print_test(out, &d.set, "folded tables of a link", &z.link.linked);
    }
    if what != "leaf" {
        out.push_str(&format!(
            "table: {} columns in the one-time test\n",
            z.once.s.fold.columns
        ));
    }
    if what != "key" {
        out.push_str(&format!(
            "table: {} columns of the first table and {} of the further one in a link\n",
            z.link.s.columns_first, z.link.s.columns_further
        ));
    }
    if what == "request" {
        out.push_str(&format!(
            "table: {} columns a batch; a stored copy bears {} batches\n",
            z.batch.s.fold.columns, z.batch.batches
        ));
        out.push_str(&format!(
            "smallness test: {} combinations\n",
            rng_combinations(&d.set, Scope::Request)
        ));
    }
    let a = account(&p, -1);
    let label = if what == "request" {
        "key, entry and proof"
    } else if what == "key" {
        "the key"
    } else {
        "an entry"
    };
    out.push_str(&print_accounting(&a, label, rounds, 6));
    for i in 0..p.parts.len() {
        let f = account(&p, i as i32);
        out.push_str(&format!(
            "footing: {}: of its rounds with a closeness term {} rest on a lemma of the paper that this protocol builds on (see THIRD_PARTY.md), proved there, {} on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given\n",
            p.parts[i], f.closeness[0], f.closeness[1]
        ));
    }
    for part in ["key", "entry", "proof"] {
        print_size(out, &p, part);
    }
    a.holds
}
