//! The plans of the three files that a verifier reads, ported from `blocks/frame/files.h`.
//!
//! A key file, a leaf file (`entry` in identifiers) and a proof file each begin with a header and
//! hold one or more hash chains (Fiat-Shamir transcripts). The key file and a leaf file have a
//! table's root (`plan_table_name`) before the first chain; after the first chain a proof file has
//! the request's place in its batch, and the key file a place in a binding tree of one leaf.
//!
//! Ported: `Subproofs`, `stand_in_subproofs`, `frame_shape_of`, `table_tree_of`, `ChainPlan`,
//! `FilePlan`, `new_chain`, `add_chain`, `Sized`, `sized`, `add_table_chains`, `refused_file`,
//! `file_proof`, `plan_table_name`, `file_key`, `file_entry` and `merged`. `sized_table` and the
//! prover's file writers are not ported.
//!
//! The C++ header keeps the `OneList` counter that numbers marked trees in a process-wide static.
//! The port has no mutable static: each file construction takes one `last` counter, and a caller
//! that makes one file or one plan set starts a fresh counter (`0`). The counter only numbers
//! trees within one plan; `plan_open` checks the numbers against that plan's own set, so a fresh
//! counter per file sees the same acceptance and rejection as the shared static. No output shows
//! the numbers.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use crate::field::ext::F;
use crate::frame::derive::{derive, Derived, FrameShape};
use crate::frame::lin_frame::{
    lin_lines, lin_plan_first, lin_plan_second, lin_plan_shared, lin_sized, LinSized,
};
use crate::frame::link_frame::{link_lines, link_plan, link_sized, LinkSized};
use crate::frame::parameters::Parameters;
use crate::frame::wf_frame::{wf_lines, wf_plan, wf_sized, WfShape, WfShapeLookup, WfSized};
use crate::iop::batt::batt_masks;
use crate::iop::context::tree_sizes;
use crate::iop::iopp::iopp_stages;
use crate::iop::member::plan_member_rows;
use crate::iop::relation::{Codes, OracleShape};
use crate::iop::req::{
    req_fault, req_groups, req_load, req_plan, ReqLink, ReqMessage, ReqShape, ReqSizes, ReqSubPlan,
};
use crate::iop::send_pad::{mask_rows_for, sample_cube};
use crate::iop::wf::{wf_index_mask_entries, WfMatrix, WfPublic, WfRun};
use crate::numbers::blocks::{
    plan_bat_sigma, plan_batt, plan_chain, plan_chain_start, plan_file_item, plan_lkp,
    plan_product_tree, plan_psc, plan_record, plan_rng, plan_scalars, plan_seal, plan_send,
    plan_shift, plan_zero, PscSize, SampleSize, TableSize, TestedIn, TreeSize,
};
use crate::numbers::codes::ceil_log2;
use crate::numbers::plan::{MessageKind, Plan, Planned};
use crate::numbers::setting::{Scope, Setting};

/// The caller's data on a request's sub-proofs and on the committer's range proof (`Subproofs`,
/// files.h:41-57). `request`: the segments with their oracle messages; `sized` completes its codes,
/// masks, answers, last test and choice. `plan`: appends a sub-proof's rounds after one commit
/// point. `after_links`: rounds after the segments' last test; may be empty. `ranges`: what WF
/// looks up, entry by entry.
#[derive(Clone)]
pub struct Subproofs {
    pub request: ReqShape,
    /// For each segment: the number of its open claims.
    pub open_rows: Vec<u64>,
    /// A sub-proof's planner. `None` stands for an empty C++ `std::function`; calling it would
    /// throw there and ends the process here. `Rc` so that a planning call can keep the sub-proofs
    /// after `configure` has taken a copy.
    pub plan: Option<Rc<ReqSubPlan<'static>>>,
    /// The number of a request's pending claims.
    pub pending_rows: u64,
    /// Rounds after the segments' last test.
    pub after_links: Option<Rc<dyn Fn(&mut Plan)>>,
    pub ranges: WfShape,
}

impl Default for Subproofs {
    /// The C++ member defaults (files.h:41-57): one pending claim, no sub-plan, no after-links.
    fn default() -> Self {
        Subproofs {
            request: ReqShape::default(),
            open_rows: Vec::new(),
            plan: None,
            pending_rows: 1,
            after_links: None,
            ranges: WfShape::default(),
        }
    }
}

/// A placeholder for planning without a model's sub-proofs (`stand_in_subproofs`, files.h:64-118).
/// Its 3,076,096 matrix rows are from the public shape of Llama 4 Maverick (no weight); of its
/// other numbers nothing is claimed. 25 segments, each with 77 rows over F at commit point 0, 7
/// read by the next segment; one row over E; 31 rows of digits and multiplicities.
pub fn stand_in_subproofs() -> Subproofs {
    fn message(
        name: &str,
        rows: usize,
        deg: u32,
        mask_rows: usize,
        moment: u32,
        life: u32,
    ) -> ReqMessage {
        ReqMessage {
            shape: OracleShape {
                name: String::from(name),
                code: 0,
                main_rows: rows,
                main_deg: deg,
                mask_rows,
                mask_code: 0,
                ..OracleShape::default()
            },
            leaf_class: 0,
            moment,
            life,
        }
    }
    let mut s = Subproofs::default();
    for l in 0..25u32 {
        let mut link = ReqLink::default();
        link.name = alloc::format!("link {}", l + 1);
        link.messages = alloc::vec![
            message("cells", 63, 1, 1, 0, 0),
            message("multiplicities", 7, 1, 0, 0, 0),
            message(
                "cells that the next link reads",
                7,
                1,
                0,
                0,
                if l + 1 < 25 { 1 } else { 0 },
            ),
            message("reads", 1, 3, 0, 1, 0),
            message("digits", 27, 1, 0, 2, 0),
            message("digits' multiplicities", 4, 1, 0, 2, 0),
        ];
        link.plain = if l + 1 == 25 { 1 } else { 0 };
        s.request.link.push(link);
    }
    s.open_rows = alloc::vec![1u64 << 13; 25];
    {
        // 3,076,096 rows of bytes; 1,527,800 pairs of them, in one run, are the two digits of
        // weights.
        s.ranges.matrix_rows = 3076096;
        let mut bytes = WfShapeLookup::default();
        bytes.lookup.name = String::from("bytes");
        bytes.lookup.d = 8;
        bytes.lookup.digit_weight = alloc::vec![F::one()];
        bytes.lookup.offset = F::from_u64(128);
        bytes.lookup.first_bound = alloc::vec![2, 1, 0, 5, 4, 3, 8, 7, 6];
        bytes.log_rows_apart = 1;
        let mut weights = WfShapeLookup::default();
        weights.lookup.name = String::from("weights");
        weights.lookup.d = 13;
        weights.lookup.digit_weight = alloc::vec![F::one(), F::from_u64(256)];
        weights.lookup.offset = F::from_u64(4096);
        weights.lookup.first_bound = bytes.lookup.first_bound.clone();
        weights.entries = alloc::vec![WfRun {
            first_place: 0,
            first_row: 0,
            places: 1527800,
            stride: 1527800,
        }];
        bytes.entries = alloc::vec![
            weights.entries[0],
            WfRun { first_place: 0, first_row: 3055600, places: 10248, stride: 10248 },
        ];
        s.ranges.lookups = alloc::vec![bytes, weights];
    }
    s.plan = Some(Rc::new(|p: &mut Plan, _link: usize, moment: u32, _last: &mut u64| {
        if moment == 0 {
            for _ in 0..2 {
                plan_shift(p, "look-up", 1u64 << 21);
                plan_lkp(p, "look-up", 28);
                plan_product_tree(p, "look-up, keys", 28, 0);
                plan_product_tree(p, "look-up, table", 16, 5);
            }
            for _ in 0..4 {
                let x = PscSize {
                    degree: alloc::vec![4; 24],
                    degree_y: 3,
                    values: 3,
                    ..PscSize::default()
                };
                plan_zero(p, "relations", 24);
                plan_psc(p, "relations", &x);
            }
        } else if moment == 1 {
            plan_rng(p, "smallness", 1u64 << 16);
        } else {
            plan_lkp(p, "digits' look-up", 26);
            plan_product_tree(p, "digits' look-up", 26, 0);
            plan_batt(p, "rows on the table", 14, 22);
            plan_scalars(p, "scalars", "stand-in", 560);
            plan_bat_sigma(p, "smallness", 1u64 << 14);
        }
    }));
    s.pending_rows = 13;
    s
}

/// What `derive` needs from the sub-proofs' shapes (`frame_shape_of`, files.h:124-135). Of the two
/// codes only the message lengths are used: `derive` has yet to fix their random tails. 4096 is
/// assumed, not checked, to be at least the number of positions drawn on a segment's group.
pub fn frame_shape_of(par: &Parameters, sub: &Subproofs) -> FrameShape {
    let mut shape = sub.request.clone();
    shape.answers = par.answers;
    let load = req_load(&shape, par.link.log_ell, par.link.mask_log_ell, &sub.open_rows);
    let mut f = FrameShape {
        link_rows_log: load.k,
        link_slots: load.slots,
        link_cube_bits: load.cube_bits,
        link_batched_rows: load.rows + load.rows_a_draw * 4096,
        last_rows_log: req_groups(&shape).last().unwrap().k,
        ..FrameShape::default()
    };
    for l in &shape.link {
        f.link_messages = core::cmp::max(f.link_messages, (2 * l.messages.len() + 2) as u32);
    }
    f.index_rows = sub.ranges.matrix_rows;
    f
}

/// How the committed table's columns are hashed: a tree leaf contains one symbol of every row
/// (`table_tree_of`, files.h:138-142).
pub fn table_tree_of(s: &Setting, par: &Parameters) -> TreeSize {
    TreeSize {
        name: String::from("table"),
        log_n: par.table_log_n,
        leaf_bytes: (s.f_bytes as u64) << par.table_rows_log,
        ..TreeSize::default()
    }
}

/// One chain of a file (`ChainPlan`, files.h:144-147).
#[derive(Clone, Debug)]
pub struct ChainPlan {
    pub name: String,
    pub plan: Rc<Planned>,
}

/// A file's plan (`FilePlan`, files.h:150-156). `has_place`: after the first chain comes the place
/// in the binding tree, a Merkle tree over the seals of a batch's first chains.
#[derive(Clone, Debug, Default)]
pub struct FilePlan {
    pub name: String,
    /// Of 4 bytes: tag, version and, in a proof file, the leaf table number.
    pub head_words: u32,
    pub chains: Vec<ChainPlan>,
    /// The binding tree's depth.
    pub place_depth: u32,
    pub has_place: bool,
}

/// A chain is made once per request, batch or commitment; its rounds' proof of work depends on it
/// (`new_chain`, files.h:161-166). `compact`: equal rounds may be planned once, with a count.
pub fn new_chain(s: &Setting, scope: Scope, compact: bool) -> Plan {
    let mut p = Plan::new(s.clone());
    p.compact = compact;
    p.begin_scope(scope);
    p
}

/// `add_chain` (files.h:167).
pub fn add_chain(f: &mut FilePlan, name: &str, p: &Plan) {
    f.chains.push(ChainPlan { name: String::from(name), plan: p.finish() });
}

/// What the three files' plans are made from (`Sized`, files.h:172-181).
#[derive(Clone, Debug, Default)]
pub struct Sized {
    pub par: Parameters,
    pub d: Derived,
    pub proof_codes: Codes,
    pub key_codes: Codes,
    pub entry_codes: Codes,
    /// `Subproofs::request`, completed by `sized`.
    pub request: ReqShape,
    /// LIN for a batch, and as the committer's one-time test.
    pub batch: LinSized,
    pub once: LinSized,
    /// The committer's proof that the table's entries are in their ranges.
    pub ranges: WfSized,
    pub link: LinkSized,
    /// Not empty: why sizing failed; not all fields are filled.
    pub refused: String,
}

/// `sized` (files.h:182-229).
pub fn sized(par: &Parameters, sub: &Subproofs) -> Sized {
    let mut z = Sized { par: par.clone(), ..Sized::default() };
    let shape = frame_shape_of(par, sub);
    z.d = derive(par, &shape);
    z.refused = z.d.refused.clone();
    if !z.refused.is_empty() {
        return z;
    }
    let s = z.d.set.clone();
    z.request = sub.request.clone();
    // Adds the segments' two codes first: they get number 0.
    z.request.last = iopp_stages(&z.d.last.stages, &mut z.proof_codes);
    z.request.code = 0;
    z.request.mask_code = 0;
    z.request.answers = par.answers;
    z.request.choice.masks_ride = true;
    {
        let mut lines = lin_lines(par, &shape, false);
        // No parameter line gives the index-mask message's number of mask rows. It follows from
        // the mask entries used: one for each pending claim and, if there are several, those of
        // BATT, which batches them into one.
        lines.input_mask_rows = mask_rows_for(
            sub.pending_rows
                + if sub.pending_rows > 1 { batt_masks(par.block_log) as u64 } else { 0 },
            1usize << par.own.mask_log_ell,
            par.answers,
        );
        if lines.input_mask_rows == 0 {
            z.refused = String::from(
                "own: no number of mask rows holds the entries that a request's rows on the table take",
            );
            return z;
        }
        z.batch = lin_sized(&s, &lines, &z.d.table, &mut z.proof_codes);
    }
    if !z.batch.refused.is_empty() {
        z.refused = z.batch.refused.clone();
        return z;
    }
    // The index-mask message is sent in the request's first prover message. It is opened at the
    // positions of the second chain's proximity test and of no segment's, so it gets its own leaf
    // class and thus its own Merkle tree.
    let mut masks = z.batch.input.clone();
    masks.leaf_class = 0;
    for l in &z.request.link {
        for m in &l.messages {
            masks.leaf_class = core::cmp::max(masks.leaf_class, m.leaf_class.wrapping_add(1));
        }
    }
    z.request.at_start.push(masks);
    if let Some(fault) = req_fault(&z.proof_codes, &z.request) {
        z.refused = String::from(fault);
        return z;
    }
    {
        let mut ranges = sub.ranges.clone();
        ranges.k_col = par.block_log;
        let of_the_ranges = wf_lines(&ranges, &par.once_ranges, par.ranges_part);
        // Of its fields, the count below depends only on `lookups` and their parts.
        let look_ups = WfPublic { lookups: of_the_ranges.lookups.clone(), ..WfPublic::default() };
        let mut lines = lin_lines(par, &shape, true);
        lines.input_mask_rows = mask_rows_for(
            wf_index_mask_entries(
                &look_ups,
                &WfMatrix { k_col: of_the_ranges.k_col, rows: of_the_ranges.matrix_rows },
            ) as u64,
            1usize << par.once_own.mask_log_ell,
            par.answers,
        );
        if lines.input_mask_rows == 0 {
            z.refused = String::from(
                "once-own: no number of mask rows holds the entries that the ranges and the joining take",
            );
            return z;
        }
        z.once = lin_sized(&s, &lines, &z.d.table, &mut z.key_codes);
        if !z.once.refused.is_empty() {
            z.refused = z.once.refused.clone();
            return z;
        }
        z.ranges = wf_sized(&s, &of_the_ranges, &mut z.key_codes);
        if !z.ranges.refused.is_empty() {
            z.refused = z.ranges.refused.clone();
            return z;
        }
    }
    z.link = link_sized(&s, &link_lines(par), &z.d.table, &mut z.entry_codes);
    z.refused = z.link.refused.clone();
    z
}

/// LIN's shared chain and second chain, after the chain that leaves LIN's claim
/// (`add_table_chains`, files.h:254-268). `x`: LIN for a batch, or as the committer's one-time
/// test. In this file only the shared chain starts without a salt.
pub fn add_table_chains(
    f: &mut FilePlan,
    s: &Setting,
    par: &Parameters,
    codes: &Codes,
    x: &LinSized,
    compact: bool,
    last: &mut u64,
) {
    {
        let mut p = new_chain(
            s,
            if x.lines.one_time { Scope::Once } else { Scope::Shared },
            compact,
        );
        plan_chain_start(&mut p, "shared chain", false);
        lin_plan_shared(&mut p, codes, x, &table_tree_of(s, par), last);
        plan_seal(&mut p, "shared chain");
        add_chain(f, "shared chain", &p);
    }
    {
        let mut p = new_chain(
            s,
            if x.lines.one_time { Scope::Once } else { Scope::Request },
            compact,
        );
        plan_chain_start(&mut p, "second chain", true);
        let input_trees = tree_sizes(codes, core::slice::from_ref(&x.input), last);
        lin_plan_second(&mut p, codes, x, &input_trees, last);
        add_chain(f, "second chain", &p);
    }
}

/// If `z` was rejected, gives `f` a rejected plan for each named chain and returns true
/// (`refused_file`, files.h:272-280). Such a plan does not meet its target and cannot be run.
pub fn refused_file(f: &mut FilePlan, z: &Sized, chains: &[&str]) -> bool {
    if z.refused.is_empty() {
        return false;
    }
    for name in chains {
        let mut p = new_chain(&z.d.set, Scope::Request, true);
        p.refuse(&z.refused);
        add_chain(f, name, &p);
    }
    true
}

/// A proof file: header | first chain (the request's own) | its place in the batch | shared chain
/// (one for the whole batch) | second chain (the request's own again) (`file_proof`,
/// files.h:286-304). `sub` must be the `Subproofs` that `z` was sized from; this does not compare
/// them. `last` is the caller's fresh `OneList` counter.
pub fn file_proof(z: &Sized, sub: &Subproofs, compact: bool, last: &mut u64) -> FilePlan {
    let s = &z.d.set;
    let mut f = FilePlan { name: String::from("proof"), head_words: 3, ..FilePlan::default() };
    if refused_file(&mut f, z, &["first chain", "shared chain", "second chain"]) {
        return f;
    }
    {
        let mut p = new_chain(s, Scope::Request, compact);
        plan_chain_start(&mut p, "first chain", true);
        // `at_start` is tested in LIN's `own` group.
        let sizes = ReqSizes {
            group: z.d.link.group.clone(),
            last: z.d.last.stages.clone(),
            rows: sub.open_rows.clone(),
            at_start: z.batch.own.stages[0].g.clone(),
        };
        let sub_plan = sub.plan.as_deref().expect("files: a request's sub-plan is empty");
        req_plan(&mut p, &z.proof_codes, &z.request, &sizes, sub_plan, last);
        if let Some(after) = &sub.after_links {
            after(&mut p);
            p.begin_scope(Scope::Request); // it may have changed the scope
        }
        // BATT, if several: the pending claims into one.
        plan_member_rows(&mut p, "rows on the table", sub.pending_rows, z.batch.s.k_col());
        lin_plan_first(&mut p, &z.proof_codes, &z.batch);
        plan_seal(&mut p, "first chain");
        add_chain(&mut f, "first chain", &p);
    }
    add_table_chains(&mut f, s, &z.par, &z.proof_codes, &z.batch, compact, last);
    f.has_place = true;
    f.place_depth = ceil_log2(z.par.slots);
    f
}

/// A committed table's root and its record (`plan_table_name`, files.h:310-313). They are items of
/// the file before the chain, not messages of the chain.
pub fn plan_table_name(p: &mut Plan, where_: &str, t: &TableSize) {
    let digest = p.set.digest_bytes as u64;
    plan_file_item(p, "root", where_, MessageKind::Root, digest, digest as f64, 0);
    plan_record(p, where_, t);
}

/// The key file: header | the anchor's root and record | one-time chain | place, in a binding tree
/// of one leaf | shared chain and second chain (`file_key`, files.h:318-336).
pub fn file_key(z: &Sized, compact: bool, last: &mut u64) -> FilePlan {
    let s = &z.d.set;
    let mut f = FilePlan { name: String::from("key"), head_words: 2, ..FilePlan::default() };
    if refused_file(&mut f, z, &["one-time chain", "shared chain", "second chain"]) {
        return f;
    }
    {
        let mut p = new_chain(s, Scope::Once, compact);
        plan_table_name(&mut p, "table", &z.once.table);
        plan_chain_start(&mut p, "one-time chain", true);
        plan_send(
            &mut p,
            "masks of the committer's rows on the table",
            &[SampleSize {
                cube_bits: sample_cube(&z.key_codes, &z.once.input.shape).bits,
                groups: TestedIn::new(&z.once.own.stages[0].g),
            }],
            1,
            true,
        );
        // With BATT on the pending claims that it leaves.
        wf_plan(&mut p, &z.key_codes, &z.ranges, last);
        lin_plan_first(&mut p, &z.key_codes, &z.once);
        plan_seal(&mut p, "one-time chain");
        add_chain(&mut f, "one-time chain", &p);
    }
    add_table_chains(&mut f, s, &z.par, &z.key_codes, &z.once, compact, last);
    f.has_place = true;
    f.place_depth = 0; // the binding tree of a batch of one
    f
}

/// A leaf file: header | the leaf table's root and record | one chain: the LINK proof
/// (`file_entry`, files.h:340-351).
pub fn file_entry(z: &Sized, compact: bool, last: &mut u64) -> FilePlan {
    let s = &z.d.set;
    let mut f = FilePlan { name: String::from("entry"), head_words: 2, ..FilePlan::default() };
    if refused_file(&mut f, z, &["link's chain"]) {
        return f;
    }
    let mut p = new_chain(s, Scope::Once, compact);
    plan_table_name(&mut p, "further table", &z.link.table);
    plan_chain_start(&mut p, "link's chain", true);
    link_plan(&mut p, &z.entry_codes, &z.link, &table_tree_of(s, &z.par), last);
    add_chain(&mut f, "link's chain", &p);
    f
}

/// Joins several files into one plan, for the error accounting, the lengths and the list of fields
/// (`merged`, files.h:356-372). A chain that was rejected, or whose errors were computed under a
/// `Setting` other than `s`, causes the joined plan to be rejected.
pub fn merged(s: &Setting, files: &[FilePlan]) -> Rc<Planned> {
    let first = if files.is_empty() { "proof" } else { files[0].name.as_str() };
    let mut p = Plan::with_first_part(s.clone(), first);
    for f in files {
        p.begin_part(&f.name);
        plan_file_item(
            &mut p,
            "head",
            "",
            MessageKind::Head,
            4 * f.head_words as u64,
            4.0 * f.head_words as f64,
            0,
        );
        for (i, chain) in f.chains.iter().enumerate() {
            plan_chain(&mut p, &chain.plan);
            if i != 0 || !f.has_place {
                continue;
            }
            // With the first chain's seal, the next three items give the binding tree's root,
            // which is in the shared chain's first query.
            plan_file_item(&mut p, "place in the batch", "", MessageKind::Head, 8, 8.0, 0);
            plan_file_item(
                &mut p,
                "salt of the place's leaf",
                "",
                MessageKind::Salts,
                s.salt_bytes as u64,
                s.salt_bytes as f64,
                1,
            );
            plan_file_item(
                &mut p,
                "path in the batch",
                "",
                MessageKind::Paths,
                f.place_depth as u64 * s.digest_bytes as u64,
                f.place_depth as f64 * s.digest_bytes as f64,
                f.place_depth as u64,
            );
        }
    }
    p.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_stand_in_has_the_cpp_numbers() {
        let s = stand_in_subproofs();
        assert_eq!(s.request.link.len(), 25);
        assert_eq!(s.open_rows.len(), 25);
        assert!(s.open_rows.iter().all(|&r| r == 1 << 13));
        assert_eq!(s.request.link[0].name, "link 1");
        assert_eq!(s.request.link[24].name, "link 25");
        assert_eq!(s.request.link[0].messages.len(), 6);
        assert_eq!(s.request.link[0].messages[0].shape.name, "cells");
        assert_eq!(s.request.link[0].messages[0].shape.main_rows, 63);
        assert_eq!(s.request.link[0].messages[0].shape.mask_rows, 1);
        assert_eq!(s.request.link[0].messages[2].life, 1);
        assert_eq!(s.request.link[24].messages[2].life, 0);
        assert_eq!(s.request.link[24].plain, 1);
        assert_eq!(s.pending_rows, 13);
        assert_eq!(s.ranges.matrix_rows, 3076096);
        assert_eq!(s.ranges.lookups.len(), 2);
        assert_eq!(s.ranges.lookups[0].entries.len(), 2);
        assert_eq!(s.ranges.lookups[1].entries.len(), 1);
    }

    #[test]
    fn a_rejected_sized_gives_each_file_one_rejected_chain_per_name() {
        let mut z = Sized { refused: String::from("made up"), ..Sized::default() };
        z.d.set = Setting::default();
        let mut last = 0u64;
        let f = file_key(&z, true, &mut last);
        assert_eq!(f.name, "key");
        assert_eq!(f.head_words, 2);
        assert!(!f.has_place);
        assert_eq!(f.chains.len(), 3);
        for (i, name) in ["one-time chain", "shared chain", "second chain"].iter().enumerate() {
            assert_eq!(f.chains[i].name, *name);
            assert!(f.chains[i].plan.refused());
            assert_eq!(f.chains[i].plan.why_not(), "made up");
        }
        let e = file_entry(&z, true, &mut last);
        assert_eq!(e.name, "entry");
        assert_eq!(e.chains.len(), 1);
        assert_eq!(e.chains[0].name, "link's chain");
        let p = file_proof(&z, &stand_in_subproofs(), true, &mut last);
        assert_eq!(p.name, "proof");
        assert_eq!(p.head_words, 3);
        assert_eq!(p.chains.len(), 3);
    }

    #[test]
    fn merged_lays_out_the_heads_and_the_place() {
        let s = Setting::default();
        let mut last = 0u64;
        let z = Sized { refused: String::from("no"), ..Sized::default() };
        let files = alloc::vec![file_key(&z, true, &mut last), file_entry(&z, true, &mut last)];
        let p = merged(&s, &files);
        // Refused chains add no rounds; each file's head is one message.
        assert_eq!(p.parts.len(), 2);
        assert_eq!(p.parts[0], "key");
        assert_eq!(p.parts[1], "entry");
        assert_eq!(p.rounds.len(), 0);
        assert_eq!(p.messages.len(), 2);
        assert_eq!(p.messages[0].name, "head");
        assert_eq!(p.messages[0].bytes, 8);
        assert_eq!(p.messages[1].name, "head");
        assert_eq!(p.messages[1].bytes, 8);
    }
}
