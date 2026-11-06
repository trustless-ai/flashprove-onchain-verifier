//! The printed accounting and the record that a stage passes to the parent process, ported from
//! `blocks/numbers/accounting.h` (`print_accounting`, `print_account_group`), the stage's record
//! (`verifier/src/vf_accounting_record.h`, `acctLinesH`), `oneTimeLine()` and the line "work:" of
//! a stage (`vf_common.h`). The C++ prints to standard output; the port returns the text.

use alloc::format;
use alloc::string::String;

use crate::stage_state::WorkNote;
use crate::verifier::common::ONE_TIME_LINE_START;

use super::accounting::{AccountGroup, Accounting};
use super::real::cut2;

/// `floor(1e6 * x) / 1e6`: how `acctLinesH()` truncates a figure.
fn cut6(x: f64) -> f64 {
    if x.is_finite() {
        libm::floor(1e6 * x) / 1e6
    } else {
        x
    }
}

/// `acctLinesH()` (`vf_accounting_record.h:56-83`): a stage's record of its accounting.
pub fn acct_lines(a: &Accounting) -> String {
    if !a.formed || !a.holds {
        return String::new();
    }
    let mut o = format!(
        "plan-sums: {} {} {:.6} {:.6} {} {} {}\n",
        a.rounds,
        a.queries,
        cut6(a.sum),
        cut6(a.sum_lists),
        a.counted as u8,
        a.calls,
        a.planned_calls
    );
    o.push_str(&format!(
        "plan-rests: {} {} {} {} {} {}",
        a.target,
        a.digest_bits,
        a.needs_work as u8,
        a.closeness[0],
        a.closeness[1],
        a.circle as u8
    ));
    for kind in &a.work {
        for &g in kind {
            o.push_str(&format!(" {}", g));
        }
    }
    o.push_str(&format!(
        "\nplan-near: {} {} {} {} {} {}",
        a.near, a.near_small, a.near_closeness[0], a.near_closeness[1], a.by_work, a.on_a_word
    ));
    o.push_str(&format!("\nplan-worst: {}\n", a.worst));
    let mut group = |head: &str, g: &AccountGroup| {
        o.push_str(&format!(
            "{} {:.6} {} {} {} {}\n",
            head,
            cut6(g.bits),
            g.work,
            g.rounds,
            g.list as u8,
            g.name
        ));
    };
    group("plan-lists:", &a.lists);
    for g in a.groups.iter().take(6) {
        group("plan-round:", g);
    }
    if a.small_columns != 0 {
        o.push_str(&format!(
            "plan-union: {:.6} {} {} {} {}\n",
            cut6(a.small_union.bits),
            a.small_union.work,
            a.small_union.rounds,
            a.small_columns,
            a.small_union.name
        ));
    }
    o
}

/// `oneTimeLine()` (`vf_common.h:591-594`).
pub fn one_time_line(what: &str, lemma: u64, assumed: u64) -> String {
    format!(
        "{}the plan of {}: {} closeness rounds rest on the theorem on codes (ePrint 2025/2055, Thm 4.6), taken as given, {} on the bound within a third of the distance; the table has a record",
        ONE_TIME_LINE_START, what, assumed, lemma
    )
}

/// `workNoteLine()` (`vf_common.h:752-757`).
pub fn work_note_line(note: &WorkNote) -> String {
    if !note.needed {
        return String::new();
    }
    format!(
        "work: {:.2} + {} (one round's error without its work, in bits, + its bits of work; {})\n",
        libm::floor(100.0 * note.bits) / 100.0,
        note.work,
        note.where_
    )
}

/// `print_account_group()` (`accounting.h:252-259`).
pub fn print_account_group(head: &str, g: &AccountGroup) -> String {
    let tail = if g.holds { "" } else { "  ABOVE THE TARGET" };
    if g.work != 0 {
        format!(
            "{}  2^-{:.2} = {:.2} by the {} + {} by work, {} round(s): {}{}\n",
            head,
            cut2(g.all()),
            cut2(g.bits),
            if g.list { "lists" } else { "bound" },
            g.work,
            g.rounds,
            g.name,
            tail
        )
    } else {
        format!(
            "{}  2^-{:.2}, {} round(s): {}{}\n",
            head,
            cut2(g.all()),
            g.rounds,
            g.name,
            tail
        )
    }
}

/// `print_accounting()` (`blocks/numbers/accounting.h:273-384`). The C++ prints; the port returns
/// the text. `what`: which files it is about; `rounds_listed`: `print_rounds` has printed every
/// group above; `top`: at most how many groups are listed.
pub fn print_accounting(a: &Accounting, what: &str, rounds_listed: bool, top: usize) -> String {
    if !a.refused.is_empty() {
        return format!(
            "accounting: THE PARAMETERS ARE NOT ADMITTED: {}\naccounting: THE ROUNDS: NO: the parameters are not admitted\n",
            a.refused
        );
    }
    if !a.formed {
        return String::from("accounting: none was formed: the plan has no round with an error\n");
    }
    let kind = ["field", "sample", "closeness", "positions", "smallness", ""];
    let w = a.groups[0].all();
    let d = a.digest_bits as f64;
    let work = a.any_work();
    let mut o = format!(
        "accounting: {}: soundness round by round{}\n",
        what,
        if rounds_listed {
            " (every round's error is printed above, in the lines \"round:\")"
        } else {
            ""
        }
    );
    o.push_str(&format!(
        "accounting: target: {} bits in every round{}\n",
        a.target,
        if work {
            ", proof of work counted; every list of positions is derived from the target less the work before its draw"
        } else {
            "; no round has proof of work; every list of positions is derived from the target"
        }
    ));
    o.push_str(
        "accounting: work, bits before a verifier's message, by the kind of its error (a request's own rounds / a batch's shared / the committer's):",
    );
    for i in 0..5 {
        if a.work[i][0] != 0 || a.work[i][1] != 0 || a.work[i][2] != 0 {
            o.push_str(&format!(
                " {} {} / {} / {};",
                kind[i], a.work[i][0], a.work[i][1], a.work[i][2]
            ));
        }
    }
    o.push_str(if work { "\n" } else { " none\n" });
    o.push_str(&format!(
        "accounting: THE LARGEST ROUND ERROR: 2^-{:.2}, in the round \"{}\". Each round's error is compared with the target by itself: the rounds' errors are not added to one another. There are {} rounds, {} of them with a verifier's message.\n",
        cut2(w),
        a.worst,
        a.rounds,
        a.queries
    ));
    o.push_str(&format!(
        "accounting: rounds that hold with less than 0.01 bit to spare{}: {}: {} of the smallness test, {} with a closeness term ({} of these on the theorem on codes, ePrint 2025/2055, Theorem 4.6, taken as given), {} others\n",
        if work { ", work counted" } else { "" },
        a.near,
        a.near_small,
        a.near_closeness[0] + a.near_closeness[1],
        a.near_closeness[1],
        a.near - a.near_small - a.near_closeness[0] - a.near_closeness[1]
    ));
    o.push_str("accounting: the rounds with the largest errors (# stands for a number):\n");
    for g in a.groups.iter().take(top) {
        o.push_str(&print_account_group("accounting: ", g));
    }
    if !a.holds {
        o.push_str(&format!("accounting: THE ROUNDS: NO: {}\n", a.why_not));
    } else if !a.needs_work {
        o.push_str(
            "accounting: THE ROUNDS: HOLD: every round holds at the target, and none needs proof of work for it\n",
        );
    } else {
        o.push_str(&format!(
            "accounting: THE ROUNDS: HOLD WITH WORK: {:.2} + {}: all rounds hold at the target, {} of them only because their proof of work is counted; the pair is one round's: of all rounds the one with the largest error when work is left out, 2^-{:.2}, and its bits of work\n",
            cut2(a.lists.bits),
            a.lists.work,
            a.by_work,
            cut2(a.lists.bits)
        ));
        o.push_str(&format!(
            "work: {:.2} + {} ({}: {})\n",
            cut2(a.lists.bits),
            a.lists.work,
            what,
            a.lists.name
        ));
    }
    if a.holds {
        if a.counted {
            o.push_str(&format!(
                "accounting: hash calls: t, the prover's, is a free variable; q_V, the verifier's own in this run: {}\n",
                a.calls
            ));
        } else {
            o.push_str(&format!(
                "accounting: hash calls: t, the prover's, is a free variable; q_V, the verifier's own, is counted in a checking run (a planning call reads no file)\naccounting:   planned for chains and openings: {} (not planned: hashing of public files and tables; words that a draw skips); it stands for q_V in the lines below\n",
                a.planned_calls
            ));
        }
        let qv = if a.counted { a.calls as f64 } else { a.planned_calls as f64 };
        let bare = if work {
            format!("; in the first, proof of work is counted (without it: 2^-{:.2})", cut2(a.lists.bits))
        } else {
            String::new()
        };
        o.push_str(&format!(
            "accounting: compiled bound: (t + q_V + 1) 2^-{:.2} + 17/2 (t + q_V)^2 / 2^{}; the second term is the digests' ({} bits){}\n",
            cut2(w),
            a.digest_bits,
            a.digest_bits,
            bare
        ));
        for lt in [64, 96, 120] {
            let q = libm::ldexp(1.0, lt) + qv;
            o.push_str(&format!(
                "accounting:   at t = 2^{}: 2^-{:.2} + 2^-{:.2}{}\n",
                lt,
                cut2(w - libm::log2(q + 1.0)),
                cut2(d - libm::log2(8.5) - 2.0 * libm::log2(q)),
                if work { " (proof of work counted)" } else { "" }
            ));
        }
        let bare = if work {
            format!(
                ", proof of work counted (without it: {:.2} bits)",
                cut2(super::accounting::compiled_level(a.lists.bits, a.digest_bits))
            )
        } else {
            String::new()
        };
        o.push_str(&format!(
            "accounting: as one number, by the compiled bound: {:.2} bits{}: the largest L such that a prover with at most 2^L hash calls, the verifier's counted in, succeeds with probability at most (its calls) / 2^L\n",
            cut2(super::accounting::compiled_level(w, a.digest_bits)),
            bare
        ));
    }
    o.push_str(&format!(
        "accounting: what stands behind it:\naccounting:   of the rounds with a closeness term {} rest on a lemma of the paper that this protocol builds on (see THIRD_PARTY.md), proved there (within a third of a code's distance; the same bound is also in other papers: blocks/numbers/codes.h names them)\n",
        a.closeness[0]
    ));
    if a.closeness[1] != 0 {
        o.push_str(&format!(
            "accounting:   {} of them rest on the theorem on codes, Theorem 4.6 of ePrint 2025/2055, which we take as given and of which we have verified no proof ourselves (blocks/numbers/codes.h says what the posting of November 6, 2025 prints behind it): TAKEN AS GIVEN\n",
            a.closeness[1]
        ));
    } else {
        o.push_str("accounting:   none of them rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6)\n");
    }
    let beyond = a.closeness[1] != 0;
    if beyond {
        o.push_str("accounting:   beyond a third a fold's round has no factor for the number of interleaved rows (a bound argued on paper for this protocol, for linear codes over E and two tables combined by one challenge; see docs/limits.md)\n");
    }
    if beyond || a.closeness[0] != 0 {
        o.push_str("accounting:   a fold of 2^v rows at one point counts v closeness terms (a bound argued on paper for this protocol; see docs/limits.md)\n");
    }
    if beyond && a.circle {
        o.push_str("accounting:   over 2^61 - 1 each term beyond a third has one list size more, since the encoding's image is a subcode (a bound argued on paper for this protocol; see docs/limits.md)\n");
    }
    if beyond || a.closeness[0] != 0 {
        o.push_str("accounting:   the bounds for this protocol's own steps are argued on paper, in a technical report that is not public and not refereed: see docs/limits.md#what-the-theorem-assumes\n");
    }
    if a.small_columns != 0 {
        o.push_str("accounting:   the smallness test's round counts one column: the first that no small integer column explains, which is fixed before the draw (argued on paper for this protocol; see docs/limits.md); a union bound over all columns stands among the stricter readings\n");
    }
    o.push_str("accounting:   the blocks' round errors and the compiled bound are cited from published work, some of it not peer-reviewed, or argued on paper in a technical report that is not public and not refereed; they are not proved for these programs (the Lean library proves its own verifier's bound, not this one)\n");
    if a.on_a_word != 0 {
        o.push_str(&format!(
            "accounting:   {} round(s) have an error that is computed from a number which the parameter file or this program's own code supplies and which no check ties to the run at that round (blocks/numbers/plan.h, ON_THE_CALLERS_WORD, says which numbers; some are held at a later place; see docs/limits.md#how-the-programs-count). Not counted: the rule and the integer m under which a group's distance stands: they are the analysis's choice and no number of a run; that all rounds of one chain on the same two codes were priced under one choice is not asked by this account: the committer, the prover and the verifier ask it of each chain when they read the public files\n",
            a.on_a_word
        ));
    } else {
        o.push_str("accounting:   that all rounds of one chain on the same two codes were priced under one choice of distance is not asked by this account: the committer, the prover and the verifier ask it of each chain when they read the public files\n");
    }
    if work {
        o.push_str("accounting:   that g bits of work before a message multiply its round's error by 2^-g is assumed for this program's hash chains; it is proved for another setting in ePrint 2021/582, Theorem 6\n");
    }
    o.push_str("accounting:   that the programs compute the protocol is not proved; no figure here is a security level\n");
    o.push_str("accounting: hiding is a separate bound, in the numbers of queries and of proofs on one commitment, and is no part of these figures\n");
    o.push_str("accounting: FOR INFORMATION, stricter readings of the same rounds, which decide nothing. Each starts from the rounds' errors as they are charged above; in some rounds the charge is the largest of several events' chances and not their sum: so none is a union bound over all events\n");
    if work {
        o.push_str(&format!(
            "accounting:   the largest round error without the work: 2^-{:.2} ({})\n",
            cut2(a.lists.bits),
            a.lists.name
        ));
        o.push_str(&format!(
            "accounting:   all rounds' errors added: 2^-{:.2} with the work, 2^-{:.2} without\n",
            cut2(a.sum),
            cut2(a.sum_lists)
        ));
    } else {
        o.push_str(&format!(
            "accounting:   all rounds' errors added: 2^-{:.2}\n",
            cut2(a.sum)
        ));
    }
    if a.small_columns != 0 {
        o.push_str(&format!(
            "accounting:   the smallness test's round by a union bound over the {} columns of its matrix (their number times its error: one event a column: blocks/iop/rng.h): 2^-{:.2}{} ({})\n",
            a.small_columns,
            cut2(a.small_union.all()),
            if a.small_union.work != 0 { " with its work" } else { "" },
            a.small_union.name
        ));
    }
    o.push_str("accounting:   the unit of all figures above: one key's, one entry's and ONE request's proof; a round that the requests of a batch share is counted for all of them at once; counted jointly for a full batch of N requests, each round of a request's own chains reads log2(N) bits less (6 bits at 64)\n");
    o
}
