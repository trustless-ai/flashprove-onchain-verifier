//! The conditions that hiding puts on a configuration, ported from
//! `blocks/frame/hiding_conditions.h`.
//!
//! A function here returns `""` or the first condition missed, as `<name>: <what>`. The
//! verifier-reachable subset is ported: the list of positions, one approximate range check and its
//! bits, the tests within a proximity test and within LIN's prover messages, and the three
//! programs `hiding_conditions_missed_in_the_links`, `..._in_the_ranges`,
//! `..._on_the_table` and `hiding_conditions_missed`. Not ported: `hiding_conditions_missed_by_the_file`
//! and the prover-only helpers (the committer's running column count), which no verifier runs.
//!
//! The failure texts are the C++ texts, byte for byte. `TableUse` counts what the caller has begun
//! on a table; every verifier call takes the defaults, under which no column that a LINK proof
//! opens of the anchor is counted.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::code::code::{hiding_positions, Code};
use crate::frame::files::{
    add_table_chains, file_entry, file_key, file_proof, FilePlan, Sized, Subproofs,
};
use crate::frame::lin_frame::LinSized;
use crate::iop::context::OracleNotice;
use crate::iop::iopp::IoppStage;
use crate::iop::lin::{lin_message_omega, lin_message_u, lin_message_w, LinShape};
use crate::iop::req::req_groups;
use crate::iop::relation::Codes;
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::{MessageKind, Plan, Planned};
use crate::numbers::setting::RoundKind;

/// The number of positions that each POSITIONS round of a chain's plan draws, in order
/// (`lists_of`, hiding_conditions.h:112-117).
pub fn lists_of(p: &Planned) -> Vec<u64> {
    let mut t = Vec::new();
    for r in &p.rounds {
        if r.kind == RoundKind::Positions {
            t.push(r.draw_positions);
        }
    }
    t
}

/// One approximate range check of a request (`RangeCheck`, hiding_conditions.h:124-127). `rows`,
/// `columns`: of the integer matrix of unpacked cells. `bound`: every cell is below it in absolute
/// value. `combinations`: of each row's cells, with coefficients 0, 1 and -1. A combination must
/// lie in `[-range, range)`, represented exactly by the two digits of `digit_bits[]` bits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RangeCheck {
    pub rows: u64,
    pub columns: u64,
    pub combinations: u64,
    pub bound: u64,
    pub range: u64,
    pub digit_bits: [u32; 2],
}

/// How often a commitment's one-time test and LINK proofs have been begun (`TableUse`,
/// hiding_conditions.h:140-144). The defaults count one one-time test and one LINK proof of a leaf
/// table, and no LINK proof of the anchor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableUse {
    pub one_time_tests: u64,
    pub links_on_the_first: u64,
    pub links_on_a_copy: u64,
}

impl Default for TableUse {
    /// The C++ member defaults (hiding_conditions.h:141-143).
    fn default() -> Self {
        TableUse { one_time_tests: 1, links_on_the_first: 0, links_on_a_copy: 1 }
    }
}

/// A lower bound on -log2 of the chance that an honest prover fails the check; negative if none is
/// shown (`range_check_bits`, hiding_conditions.h:150-158).
pub fn range_check_bits(c: &RangeCheck) -> i64 {
    if c.rows == 0 || c.columns == 0 || c.combinations == 0 || c.bound < 2 || c.range == 0 {
        return -1;
    }
    if c.range >> 40 != 0
        || c.bound >> 32 != 0
        || c.columns >> 32 != 0
        || c.rows >> 40 != 0
        || c.combinations >> 16 != 0
    {
        return -1;
    }
    let bits = c.digit_bits[0].wrapping_add(c.digit_bits[1]);
    if bits > 41 || (1u64 << bits) != 2 * c.range {
        // Else the bound below is not about what is tested.
        return -1;
    }
    let above = c.range as u128 * c.range as u128 * 14426;
    let below = c.columns as u128 * (c.bound - 1) as u128 * (c.bound - 1) as u128 * 10000;
    let bits = above / below;
    if bits >> 30 != 0 {
        return 1i64 << 30;
    }
    bits as i64 - 1 - ceil_log2(c.rows) as i64 - ceil_log2(c.combinations) as i64
}

/// The one text that every missed condition below is reported with (`hiding_missed`,
/// hiding_conditions.h:160-162).
pub fn hiding_missed(name: &str, what: &str, have: u64, need: u64) -> String {
    format!("{}: {}: {} where {} are needed", name, what, have, need)
}

/// One proximity test: its list `i` is `lists[at + i]` (`hiding_missed_in_test`,
/// hiding_conditions.h:163-177). `more_main`, `more_mask`: further draws on the first stage's main
/// and mask rows. Not checked: that `lists` has `at + stages.len()` entries.
pub fn hiding_missed_in_test(
    what: &str,
    codes: &Codes,
    stages: &[IoppStage],
    lists: &[u64],
    at: usize,
    more_main: u64,
    more_mask: u64,
) -> String {
    for (i, stage) in stages.iter().enumerate() {
        let where_ = format!("{}, stage {}", what, i + 1);
        let t = lists[at + i];
        let main = hiding_positions(&codes.base[stage.code as usize]);
        let mask = hiding_positions(&codes.mask[stage.mask_code as usize]);
        let extra_main = if i != 0 { 0 } else { more_main };
        let extra_mask = if i != 0 { 0 } else { more_mask };
        if main < t.wrapping_add(extra_main) {
            return hiding_missed("main-rows", &where_, main, t.wrapping_add(extra_main));
        }
        if mask < t.wrapping_add(extra_mask) {
            return hiding_missed("mask-rows", &where_, mask, t.wrapping_add(extra_mask));
        }
        let need = 2u64
            .wrapping_mul(stage.k as u64)
            .wrapping_add(1)
            .wrapping_sub(stage.h as u64);
        if (codes.mask[stage.mask_code as usize].ell as u64) < need {
            return hiding_missed(
                "fold-room",
                &where_,
                codes.mask[stage.mask_code as usize].ell as u64,
                need,
            );
        }
    }
    String::new()
}

/// An oracle message and whose lists read it, one bit each (`ReadAt`, hiding_conditions.h:179-183).
/// `lists`: bit 1 is the test on the folded row's group, 2 the one on Omega's group, 4 a request's
/// own test.
#[derive(Clone, Debug)]
pub struct ReadAt {
    pub notice: OracleNotice,
    pub lists: u32,
}

/// The condition `leaves` within one prover message (`hiding_missed_in_leaves`,
/// hiding_conditions.h:184-191).
pub fn hiding_missed_in_leaves(where_: &str, message: &[ReadAt]) -> String {
    for i in 0..message.len() {
        for j in 0..i {
            if message[i].notice.leaf_class == message[j].notice.leaf_class
                && message[i].lists != message[j].lists
            {
                return format!(
                    "leaves: {}: {} shares leaves with {}, which is read at other lists",
                    where_,
                    message[i].notice.shape.name,
                    message[j].notice.shape.name
                );
            }
        }
    }
    String::new()
}

/// The condition `leaves` in LIN's three prover messages with oracle messages
/// (`hiding_missed_in_the_tables_leaves`, hiding_conditions.h:192-210).
pub fn hiding_missed_in_the_tables_leaves(where_: &str, s: &LinShape) -> String {
    const FOLDED: u32 = 1;
    const SECOND: u32 = 2;
    const OWN: u32 = 4;
    let split = s.shared_split_needed();
    if s.own_split_needed() {
        return format!(
            "leaves: {}: a request's own vector under another code than the second oracle's is not reckoned with here",
            where_
        );
    }
    let mut u: Vec<ReadAt> = Vec::new();
    for n in lin_message_u(s) {
        u.push(ReadAt { notice: n, lists: FOLDED });
    }
    let mut omega: Vec<ReadAt> = Vec::new();
    for (i, n) in lin_message_omega(s).into_iter().enumerate() {
        let lists = if i == 0 {
            (if split { SECOND } else { FOLDED }) | OWN
        } else if split && i == 1 {
            FOLDED | SECOND
        } else if split {
            SECOND
        } else {
            FOLDED
        };
        omega.push(ReadAt { notice: n, lists });
    }
    let mut w: Vec<ReadAt> = Vec::new();
    for n in lin_message_w(s) {
        w.push(ReadAt { notice: n, lists: OWN });
    }
    for m in [&u, &omega, &w] {
        let why = hiding_missed_in_leaves(where_, m);
        if !why.is_empty() {
            return why;
        }
    }
    String::new()
}

/// The conditions on the committed table, on LIN and on the LINK proof
/// (`hiding_conditions_missed_on_the_table`, hiding_conditions.h:212-289). `z`: from `sized` (or
/// from `sized_table` where no request's shape is known). `pending_rows`: one request's pending
/// claims.
pub fn hiding_conditions_missed_on_the_table(
    z: &Sized,
    pending_rows: u64,
    use_: &TableUse,
) -> String {
    let s = &z.d.set;
    if s.salt_bytes < 40 {
        return hiding_missed("salt", "bytes of a leaf's salt", s.salt_bytes as u64, 40);
    }
    // Before anything is planned: a planner takes the shapes' leaf classes as they are.
    for once in [false, true] {
        let why = hiding_missed_in_the_tables_leaves(
            if once { "one-time test" } else { "batch" },
            if once { &z.once.s } else { &z.batch.s },
        );
        if !why.is_empty() {
            return why;
        }
    }
    let mut batch = FilePlan::default();
    let mut one_time_test = FilePlan::default();
    let mut last = 0u64;
    add_table_chains(&mut batch, s, &z.par, &z.proof_codes, &z.batch, false, &mut last);
    let mut last = 0u64;
    add_table_chains(
        &mut one_time_test,
        s,
        &z.par,
        &z.key_codes,
        &z.once,
        false,
        &mut last,
    );
    let mut last = 0u64;
    let entry = file_entry(z, false, &mut last);
    for once in [false, true] {
        let x: &LinSized = if once { &z.once } else { &z.batch };
        let codes: &Codes = if once { &z.key_codes } else { &z.proof_codes };
        let file: &FilePlan = if once { &one_time_test } else { &batch };
        let shape = &x.s;
        let requests = if once { 1 } else { z.par.slots };
        if x.lines.requests != requests {
            return hiding_missed(
                "batch",
                if once {
                    "requests in the one-time test"
                } else {
                    "requests that the test on the table is sized for"
                },
                x.lines.requests,
                requests,
            );
        }
        let shared = lists_of(&file.chains[0].plan);
        let own = lists_of(&file.chains[1].plan);
        let split = shape.shared_split_needed();
        if shared.len() != 1 + shape.test_u.len() + if split { shape.test_omega.len() } else { 0 }
            || own.len() != shape.test_own.len()
            || own.is_empty()
        {
            return String::from(
                "main-rows: the chains of the test on the table have other lists than the columns and one for each stage",
            );
        }
        {
            let answers = z.par.answers as u64;
            let in_a_row = z.par.table_data.wrapping_add(z.par.table_random);
            let room_u = shape.fold.u.main_rows as u64
                * codes.base[shape.fold.u.code as usize].ell as u64;
            let room_omega =
                shape.omega.main_rows as u64 * codes.base[shape.omega.code as usize].ell as u64;
            let room_w = shape.w.main_rows as u64 * codes.base[shape.w.code as usize].ell as u64;
            let columns = 1u64 << shape.k_col();
            let weights_in_a_row = shape.matrix_rows << shape.k_lo;
            if z.par.table_data < weights_in_a_row.wrapping_add(3u64.wrapping_mul(answers)) {
                return hiding_missed(
                    "padding-entries",
                    "places of a row of the table",
                    z.par.table_data,
                    weights_in_a_row.wrapping_add(3u64.wrapping_mul(answers)),
                );
            }
            if room_u < in_a_row.wrapping_add(answers) {
                return hiding_missed(
                    "padding-entries",
                    "entries of the folded table's oracle message",
                    room_u,
                    in_a_row.wrapping_add(answers),
                );
            }
            if room_omega < shape.matrix_rows.wrapping_add(answers) {
                return hiding_missed(
                    "padding-entries",
                    "entries of the second oracle's message",
                    room_omega,
                    shape.matrix_rows.wrapping_add(answers),
                );
            }
            let need_w = columns.wrapping_add(if shape.w.mask_rows != 0 { 0 } else { answers });
            if room_w < need_w {
                return hiding_missed(
                    "padding-entries",
                    "entries of a request's own vector's message",
                    room_w,
                    need_w,
                );
            }
        }
        {
            // The index-mask message needs one entry for each pending claim; if there are several,
            // the hiding polynomial of their batching, 1 + 2 for each column variable; its pad.
            let mut parts = 0u64;
            for l in &z.ranges.x.lookups {
                parts = parts.wrapping_add(l.parts.len() as u64);
            }
            let pending = if !once {
                pending_rows
            } else if parts != 0 {
                parts
            } else {
                1
            };
            let need = pending
                .wrapping_add(if once { parts } else { 0 })
                .wrapping_add(if pending > 1 {
                    1u64.wrapping_add(2u64.wrapping_mul(shape.k_col() as u64))
                } else {
                    0
                })
                .wrapping_add(z.par.answers as u64);
            let room = x.input.shape.mask_rows as u64
                * codes.mask[x.input.shape.mask_code as usize].ell as u64;
            if room < need {
                return hiding_missed(
                    "mask-room",
                    if once {
                        "the masks of the committer's rows on the table"
                    } else {
                        "the masks of a request's rows on the table"
                    },
                    room,
                    need,
                );
            }
            if split {
                let apart = shape.shared_split.mask_rows as u64
                    * codes.mask[shape.shared_split.mask_code as usize].ell as u64;
                let need = 1u64.wrapping_add(z.par.answers as u64);
                if apart < need {
                    return hiding_missed(
                        "mask-room",
                        "the masks that part a row between two groups",
                        apart,
                        need,
                    );
                }
            }
        }
        let t_u = shared[1];
        let t_omega = if split { shared[1 + shape.test_u.len()] } else { t_u };
        let t_own = own[0];
        // Omega is read by the batch's test and by every request's own. The mask-only message by
        // which SPLIT parts a claim between two groups is read at both groups' lists.
        let where_ = if once { "one-time test" } else { "batch" };
        let mut why = hiding_missed_in_test(
            &format!("{}, folded table", where_),
            codes,
            &shape.test_u,
            &shared,
            1,
            if split { 0 } else { requests.wrapping_mul(t_own) },
            if split { t_omega } else { 0 },
        );
        if why.is_empty() && split {
            why = hiding_missed_in_test(
                &format!("{}, second oracle", where_),
                codes,
                &shape.test_omega,
                &shared,
                1 + shape.test_u.len(),
                requests.wrapping_mul(t_own),
                t_u,
            );
        }
        if why.is_empty() {
            why = hiding_missed_in_test(
                &format!("{}, own test", where_),
                codes,
                &shape.test_own,
                &own,
                0,
                t_omega.wrapping_add((requests - 1).wrapping_mul(t_own)),
                0,
            );
        }
        if !why.is_empty() {
            return why;
        }
    }
    let link = lists_of(&entry.chains[0].plan);
    let link_stages = z.link.s.test();
    if link.len() != 1 + link_stages.len() {
        return String::from(
            "main-rows: a link's chain has other lists than the columns and one for each stage",
        );
    }
    {
        let why = hiding_missed_in_test(
            "link of two tables",
            &z.entry_codes,
            &link_stages,
            &link,
            1,
            0,
            0,
        );
        if !why.is_empty() {
            return why;
        }
    }
    // The table's own random tail, over the life of one committed table.
    let table = Code {
        log_n: z.par.table_log_n,
        ell: z.par.table_data as usize,
        r: z.par.table_random as usize,
    };
    let a_batch = lists_of(&batch.chains[0].plan)[0];
    let one_time = lists_of(&one_time_test.chains[0].plan)[0];
    if link[0] != z.link.s.columns_first.wrapping_add(z.link.s.columns_further) {
        // Of both tables together.
        return String::from("table: a link draws other numbers of columns than its shape says");
    }
    // A leaf table's own LINK proof takes the place of a one-time test.
    let first_copy = use_
        .one_time_tests
        .wrapping_mul(one_time)
        .wrapping_add(use_.links_on_the_first.wrapping_mul(z.link.s.columns_first));
    let further_copy = use_.links_on_a_copy.wrapping_mul(z.link.s.columns_further);
    let need = core::cmp::max(first_copy, further_copy)
        .wrapping_add(z.batch.batches.wrapping_mul(a_batch));
    if hiding_positions(&table) < need {
        return hiding_missed(
            "table",
            "columns that a stored copy's random entries hide",
            hiding_positions(&table),
            need,
        );
    }
    String::new()
}

/// The conditions on the committer's range proof, with `z` from `sized`
/// (`hiding_conditions_missed_in_the_ranges`, hiding_conditions.h:303-330).
pub fn hiding_conditions_missed_in_the_ranges(z: &Sized) -> String {
    let s = &z.d.set;
    let x = &z.ranges.x;
    let mut last = 0u64;
    let key = file_key(z, false, &mut last);
    let lists = lists_of(&key.chains[0].plan);
    if lists.len() != x.stages.len() {
        return String::from(
            "main-rows: the one-time chain has other lists than one for each stage of the ranges' test",
        );
    }
    {
        let why = hiding_missed_in_test("ranges", &z.key_codes, &x.stages, &lists, 0, 0, 0);
        if !why.is_empty() {
            return why;
        }
    }
    // Every scalar that a lookup's sumchecks send is masked by one entry. Two for each part, which
    // are linear in the table's entries, take entries of the index-mask message (counted in
    // `hiding_conditions_missed_on_the_table`); all others take entries of the range proof's own
    // mask rows. Each such row gives up as many places as the pad has; all rows but one have a
    // further free entry.
    let mut entries = 0u64;
    let mut parts = 0u64;
    for l in &x.lookups {
        parts = parts.wrapping_add(l.parts.len() as u64);
    }
    for m in &key.chains[0].plan.messages {
        for l in &x.lookups {
            let at = format!("ranges: {}", l.name);
            if m.kind == MessageKind::Scalars && m.in_chain && m.where_.starts_with(&at) {
                entries = entries.wrapping_add(m.count.wrapping_mul(m.bytes / s.e_bytes as u64));
            }
        }
    }
    if entries < 2u64.wrapping_mul(parts) {
        return String::from("mask-room: the ranges' look-ups send fewer scalars than two for each part");
    }
    entries -= 2u64.wrapping_mul(parts);
    let rows = x.message.shape.mask_rows as u64;
    let in_a_row = z.key_codes.mask[x.message.shape.mask_code as usize].ell as u64;
    let answers = z.par.answers as u64;
    let room = if rows != 0 && in_a_row > answers {
        rows.wrapping_mul(in_a_row - answers).wrapping_add(rows - 1)
    } else {
        0
    };
    if room < entries {
        return hiding_missed("mask-room", "the ranges' multiplicities", room, entries);
    }
    String::new()
}

/// The conditions on a request's segments and on the last proximity test; also `salt`, and `leaves`
/// in LIN's three prover messages (`hiding_conditions_missed_in_the_links`,
/// hiding_conditions.h:332-371). `z`: from `sized`.
pub fn hiding_conditions_missed_in_the_links(z: &Sized, sub: &Subproofs) -> String {
    let s = &z.d.set;
    if s.salt_bytes < 40 {
        return hiding_missed("salt", "bytes of a leaf's salt", s.salt_bytes as u64, 40);
    }
    for n in &z.request.at_start {
        for l in &z.request.link {
            for m in &l.messages {
                if m.leaf_class == n.leaf_class {
                    return format!(
                        "leaves: {} shares a leaf class with {}, which is read at another list",
                        n.shape.name, m.shape.name
                    );
                }
            }
        }
    }
    for once in [false, true] {
        let why = hiding_missed_in_the_tables_leaves(
            if once { "one-time test" } else { "batch" },
            if once { &z.once.s } else { &z.batch.s },
        );
        if !why.is_empty() {
            return why;
        }
    }

    // ---- a request's first chain: one list for each segment, then the last test's ----
    {
        let mut last = 0u64;
        let proof = file_proof(z, sub, false, &mut last);
        let lists = lists_of(&proof.chains[0].plan);
        let groups = req_groups(&z.request);
        let links = z.request.link.len();
        if lists.len() != links.wrapping_add(z.request.last.len()) {
            return String::from(
                "main-rows: a request's first chain has other lists than one for each link and each stage of the last test",
            );
        }
        let main = &z.proof_codes.base[z.request.code as usize];
        let mask = &z.proof_codes.mask[z.request.mask_code as usize];
        let plan = sub
            .plan
            .as_deref()
            .expect("hiding: a request's sub-plan is empty");
        for l in 0..links {
            let where_ = &z.request.link[l].name;
            if hiding_positions(main) < lists[l] {
                return hiding_missed("main-rows", where_, hiding_positions(main), lists[l]);
            }
            if hiding_positions(mask) < lists[l] {
                return hiding_missed("mask-rows", where_, hiding_positions(mask), lists[l]);
            }
            let need = 2u64
                .wrapping_mul(groups[l].k as u64)
                .wrapping_add(1)
                .wrapping_sub(groups[l].h as u64);
            if (mask.ell as u64) < need {
                return hiding_missed("fold-room", where_, mask.ell as u64, need);
            }
            // Each scalar of a masked sumcheck is masked by one entry of the segment's mask row.
            let mut own = Plan::new(s.clone());
            for moment in 0..z.request.link[l].moments() {
                plan(&mut own, l, moment, &mut last);
            }
            let mut entries = 0u64;
            let laid = own.finish(); // read for its messages alone
            for m in &laid.messages {
                if m.kind == MessageKind::Scalars && m.in_chain {
                    entries = entries.wrapping_add(m.count.wrapping_mul(m.bytes / s.e_bytes as u64));
                }
            }
            entries = entries.wrapping_add(z.par.answers as u64); // the mask row's own pad
            if (mask.ell as u64) < entries {
                return hiding_missed("mask-room", where_, mask.ell as u64, entries);
            }
        }
        return hiding_missed_in_test("last test", &z.proof_codes, &z.request.last, &lists, links, 0, 0);
    }
}

/// The complete test (`hiding_conditions_missed`, hiding_conditions.h:373-455). `z`: from `sized`.
/// `checks`: the range checks of one request. An empty result proves nothing by itself: the
/// written arguments for hiding are not in this repository; see the C++ comment for what no
/// function here tests.
pub fn hiding_conditions_missed(
    z: &Sized,
    sub: &Subproofs,
    checks: &[RangeCheck],
    use_: &TableUse,
) -> String {
    {
        let mut why = hiding_conditions_missed_in_the_links(z, sub);
        if why.is_empty() {
            why = hiding_conditions_missed_in_the_ranges(z);
        }
        if why.is_empty() {
            why = hiding_conditions_missed_on_the_table(z, sub.pending_rows, use_);
        }
        if !why.is_empty() {
            return why;
        }
    }
    // ---- the range checks: all of one request's, times the requests under a commitment ----
    if checks.is_empty() {
        return String::from("range-checks: the sub-proofs name none");
    }
    let mut least = 1i64 << 30;
    for c in checks {
        let bits = range_check_bits(c);
        if bits < 0 {
            return String::from(
                "range-checks: a check fails too often, its digits do not represent its range exactly, or its numbers are out of range",
            );
        }
        least = core::cmp::min(least, bits);
    }
    // The requests under a commitment: a batch's, times a table's batches, times the tables. A leaf
    // table is tied to the anchor and to no other table, by a LINK proof that opens columns of the
    // anchor: so the anchor's random tail bounds the number of leaf tables, whatever `TableUse`
    // says has been begun so far. Each factor's logarithm is rounded up by itself.
    let table = Code {
        log_n: z.par.table_log_n,
        ell: z.par.table_data as usize,
        r: z.par.table_random as usize,
    };
    let bears = hiding_positions(&table);
    let one_time = z.once.s.fold.columns;
    let copies = 1u64.wrapping_add(
        bears.saturating_sub(core::cmp::min(bears, one_time))
            / core::cmp::max(1, z.link.s.columns_first),
    );
    let have = least
        - ceil_log2(checks.len() as u64) as i64
        - ceil_log2(z.par.slots) as i64
        - ceil_log2(core::cmp::max(1, z.batch.batches)) as i64
        - ceil_log2(copies) as i64;
    if have < z.par.sec as i64 {
        return hiding_missed(
            "range-checks",
            "bits of the bound on the chance that some honest range check under a key fails",
            if have < 0 { 0 } else { have as u64 },
            z.par.sec as u64,
        );
    }
    String::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::iop::relation::OracleShape;

    #[test]
    fn a_check_outside_its_ranges_gives_minus_one() {
        let mut c = RangeCheck { rows: 1, columns: 1, combinations: 1, bound: 2, range: 2, digit_bits: [1, 1] };
        assert_eq!(range_check_bits(&c), 4);
        c.rows = 0;
        assert_eq!(range_check_bits(&c), -1);
        c.rows = 1;
        c.bound = 1;
        assert_eq!(range_check_bits(&c), -1);
        c.bound = 2;
        c.digit_bits = [1, 2];
        assert_eq!(range_check_bits(&c), -1);
    }

    #[test]
    fn a_large_check_is_capped_at_two_to_the_thirty() {
        let c = RangeCheck {
            rows: 1,
            columns: 1,
            combinations: 1,
            bound: 2,
            range: 1 << 39,
            digit_bits: [20, 20],
        };
        assert_eq!(range_check_bits(&c), 1 << 30);
    }

    #[test]
    fn the_text_is_the_cpp_text() {
        assert_eq!(
            hiding_missed("salt", "bytes of a leaf's salt", 39, 40),
            "salt: bytes of a leaf's salt: 39 where 40 are needed"
        );
    }

    fn codes(main_r: usize, mask_r: usize, mask_ell: usize) -> Codes {
        Codes {
            base: alloc::vec![Code { log_n: 8, ell: 16, r: main_r }],
            mask: alloc::vec![Code { log_n: 8, ell: mask_ell, r: mask_r }],
        }
    }

    fn stage(k: u32, h: u32) -> IoppStage {
        IoppStage { code: 0, mask_code: 0, k, h }
    }

    #[test]
    fn a_test_reports_the_first_stage_short_of_hiding() {
        let st = [stage(1, 0)];
        assert_eq!(
            hiding_missed_in_test("a test", &codes(2, 4, 16), &st, &[3], 0, 0, 0),
            "main-rows: a test, stage 1: 2 where 3 are needed"
        );
        assert_eq!(
            hiding_missed_in_test("a test", &codes(4, 2, 16), &st, &[3], 0, 0, 0),
            "mask-rows: a test, stage 1: 2 where 3 are needed"
        );
        // The mask row must fit 2k + 1 - h = 3 entries of the fold's hiding polynomial.
        assert_eq!(
            hiding_missed_in_test("a test", &codes(4, 4, 2), &st, &[1], 0, 0, 0),
            "fold-room: a test, stage 1: 2 where 3 are needed"
        );
        // The further draws are on the first stage alone: stage 2's list of 2 passes a main code
        // with 5 positions, which would fail if the 4 further draws were added there too.
        let two = [stage(1, 0), stage(0, 0)];
        assert_eq!(
            hiding_missed_in_test("a test", &codes(5, 5, 16), &two, &[1, 2], 0, 4, 4),
            ""
        );
    }

    #[test]
    fn a_leaf_class_read_at_two_lists_is_reported() {
        let n = OracleNotice {
            shape: OracleShape { name: String::from("one"), code: 0, ..OracleShape::default() },
            leaf_class: 7,
        };
        let m = OracleNotice {
            shape: OracleShape { name: String::from("two"), code: 0, ..OracleShape::default() },
            leaf_class: 7,
        };
        let message = alloc::vec![
            ReadAt { notice: n, lists: 1 },
            ReadAt { notice: m, lists: 4 },
        ];
        assert_eq!(
            hiding_missed_in_leaves("the test", &message),
            "leaves: the test: two shares leaves with one, which is read at other lists"
        );
        let same = alloc::vec![
            ReadAt { notice: message[0].notice.clone(), lists: 1 },
            ReadAt { notice: message[1].notice.clone(), lists: 1 },
        ];
        assert_eq!(hiding_missed_in_leaves("the test", &same), "");
    }

    #[test]
    fn the_batch_leaves_report_omega_and_the_shared_split() {
        let mut s = LinShape::default();
        // Omega and W are under one code (so a request's own vector is not split), while the
        // folded row is under another: Omega and the shared split are read at different lists but
        // share a leaf class.
        s.omega.code = 0;
        s.omega.name = String::from("Omega");
        s.w.code = 0;
        s.shared_split.name = String::from("the mask of the split between Omega and the folded row");
        s.shared_split_leaf_class = s.omega_leaf_class;
        assert_eq!(
            hiding_missed_in_the_tables_leaves("batch", &s),
            "leaves: batch: the mask of the split between Omega and the folded row shares leaves with Omega, which is read at other lists"
        );
    }

    #[test]
    fn the_salt_condition_is_the_first_of_the_table_and_the_links() {
        let mut z = Sized::default();
        z.d.set.salt_bytes = 39;
        assert_eq!(
            hiding_conditions_missed_on_the_table(&z, 1, &TableUse::default()),
            "salt: bytes of a leaf's salt: 39 where 40 are needed"
        );
        assert_eq!(
            hiding_conditions_missed_in_the_links(&z, &Subproofs::default()),
            "salt: bytes of a leaf's salt: 39 where 40 are needed"
        );
    }

    #[test]
    fn a_negative_range_check_has_no_bits() {
        let mut c = RangeCheck {
            rows: 1 << 45,
            columns: 1,
            combinations: 1,
            bound: 2,
            range: 2,
            digit_bits: [1, 1],
        };
        assert_eq!(range_check_bits(&c), -1);
        c.rows = 1;
        c.combinations = 1 << 17;
        assert_eq!(range_check_bits(&c), -1);
    }
}
