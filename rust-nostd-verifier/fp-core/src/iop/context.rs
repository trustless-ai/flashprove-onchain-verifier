//! The verifier's protocol context and tree book, ported from `blocks/iop/context.h`
//! (lines 46-332 and 510-564). The prover's engine, coins and drafts are not ported; this is the
//! substrate that the verifier blocks (FOLD, CS, IOPP, BASE) share.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use super::relation::{Codes, GroupId, OracleId, OracleShape, Statement};
use crate::chain::public::{Public, PublicBytes};
use crate::chain::rounds::{SentRoot, VerifierRounds};
use crate::code::code::{code_ok, Code};
use crate::field::ext::{F, E};
use crate::iop::message::Writer;
use crate::tree::opening::{receive_opening, Opening, OracleTreeShape};
use crate::tree::positions::PositionList;

/// The public half of an oracle draft (`OracleNotice`, context.h:54-57).
#[derive(Clone, Debug, Default)]
pub struct OracleNotice {
    pub shape: OracleShape,
    pub leaf_class: u32,
}

impl PublicBytes for Code {
    fn public_bytes(&self, w: &mut Writer) {
        for x in [self.log_n as u64, self.ell as u64, self.r as u64] {
            w.put_u64(x);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        if code_ok(self) {
            None
        } else {
            Some("a code's numbers are no code of this field")
        }
    }
}

impl PublicBytes for Codes {
    /// `public_bytes(Writer&, const Codes&)` (context.h:71-74).
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.base.len() as u64);
        for c in &self.base {
            c.public_bytes(w);
        }
        w.put_u64(self.mask.len() as u64);
        for c in &self.mask {
            c.public_bytes(w);
        }
    }
    fn public_fault(&self) -> Option<&'static str> {
        for c in self.base.iter().chain(self.mask.iter()) {
            if let Some(f) = c.public_fault() {
                return Some(f);
            }
        }
        None
    }
}

impl PublicBytes for OracleShape {
    /// `public_bytes(Writer&, const OracleShape&)` (context.h:77-81).
    fn public_bytes(&self, w: &mut Writer) {
        for x in [
            (if self.main_rows > 0 { self.code } else { super::relation::NONE_ID }) as u64,
            (if self.mask_rows > 0 { self.mask_code } else { super::relation::NONE_ID }) as u64,
            self.main_rows as u64,
            (if self.main_rows > 0 { self.main_deg } else { 1 }) as u64,
            self.mask_rows as u64,
            self.answers as u64,
        ] {
            w.put_u64(x);
        }
    }
    /// `public_fault(const OracleShape&)` (context.h:92-98).
    fn public_fault(&self) -> Option<&'static str> {
        if self.main_rows == 0 && self.mask_rows == 0 {
            return Some("an oracle message without rows");
        }
        if self.main_rows > 0 && self.code == super::relation::NONE_ID {
            return Some("an oracle message has main rows and names no code for them");
        }
        if self.mask_rows > 0 && self.mask_code == super::relation::NONE_ID {
            return Some("an oracle message has mask rows and names no mask code");
        }
        if self.main_rows > 0 && self.main_deg != 1 && self.main_deg != 3 {
            return Some("an oracle message's main rows are over F or over E");
        }
        None
    }
}

impl PublicBytes for OracleNotice {
    fn public_bytes(&self, w: &mut Writer) {
        self.shape.public_bytes(w);
        w.put_u64(self.leaf_class as u64);
    }
    fn public_fault(&self) -> Option<&'static str> {
        self.shape.public_fault()
    }
}

/// Which oracle messages of one prover message share a tree (`TreeLay`, context.h:107-110).
pub struct TreeLay {
    pub tree: Vec<u32>,
    pub part: Vec<u32>,
    pub shapes: Vec<OracleTreeShape>,
}

/// `lay_trees` (context.h:111-148).
pub fn lay_trees(codes: &Codes, sent: &[OracleNotice], salt_bytes: usize) -> TreeLay {
    let mut lay = TreeLay {
        tree: vec![0; sent.len()],
        part: vec![0; sent.len()],
        shapes: Vec::new(),
    };
    let mut leaf_class: Vec<u32> = Vec::new();
    for mask_only in 0..2 {
        for (i, n) in sent.iter().enumerate() {
            let s = &n.shape;
            if (s.main_rows == 0) != (mask_only == 1) {
                continue;
            }
            let mut t = 0usize;
            while t < lay.shapes.len()
                && !(leaf_class[t] == n.leaf_class
                    && (mask_only == 1
                        || lay.shapes[t].log_n == codes.base[s.code as usize].log_n))
            {
                t += 1;
            }
            if t == lay.shapes.len() {
                lay.shapes.push(OracleTreeShape::default());
                leaf_class.push(n.leaf_class);
                if mask_only == 0 {
                    lay.shapes[t].log_n = codes.base[s.code as usize].log_n;
                }
            }
            lay.tree[i] = t as u32;
        }
    }
    for (i, n) in sent.iter().enumerate() {
        let s = &n.shape;
        let t = &mut lay.shapes[lay.tree[i] as usize];
        if s.mask_rows > 0 {
            let log_n_zk = codes.mask[s.mask_code as usize].log_n;
            assert!(
                !t.has_mask() || t.log_n_zk == log_n_zk,
                "trees: mask rows of two lengths in one tree"
            );
            t.log_n_zk = log_n_zk;
        }
        lay.part[i] = t.main_symbols.len() as u32;
        t.main_symbols.push(s.main_rows * s.main_deg as usize);
        t.mask_symbols.push(s.mask_rows * 3);
    }
    for t in &mut lay.shapes {
        t.salt_bytes = salt_bytes;
        if !t.has_main() {
            t.log_n = t.log_n_zk;
        }
        assert!(
            !t.has_mask() || t.log_n_zk <= t.log_n,
            "trees: mask rows longer than the main rows above them"
        );
    }
    lay
}

/// The symbols of some oracle messages at a list of positions (`Opened`, context.h:170-175).
#[derive(Clone, Debug, Default)]
pub struct Opened {
    pub of: Vec<Vec<Column>>,
}

#[derive(Clone, Debug, Default)]
pub struct Column {
    pub main: Vec<E>,
    pub mask: Vec<E>,
}

/// The trees sent so far and each oracle message's place (`TreeBook`, context.h:178-332). The
/// prover's counters are kept as shared cells so that `adopt` has the same shape, but only the
/// verifier's paths are implemented.
pub struct TreeBook {
    salt_bytes: usize,
    run: crate::hash::modes::Digest,
    configuration: crate::hash::modes::Digest,
    trees: Vec<Tree>,
    place: Vec<Place>,
}

pub struct Tree {
    pub shape: OracleTreeShape,
    pub root: crate::hash::modes::Digest,
    pub sent: SentRoot,
    pub parts: Vec<OracleId>,
    pub one_list: bool,
    pub lists: Rc<Cell<usize>>,
    pub positions: Rc<Cell<u64>>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Place {
    pub tree: u32,
    pub part: u32,
}

impl TreeBook {
    pub fn new(
        salt_bytes: usize,
        run: &crate::hash::modes::Digest,
        configuration: &crate::hash::modes::Digest,
    ) -> Self {
        TreeBook {
            salt_bytes,
            run: *run,
            configuration: *configuration,
            trees: Vec::new(),
            place: Vec::new(),
        }
    }
    pub fn tree(&self, t: u32) -> &Tree {
        &self.trees[t as usize]
    }
    pub fn set_root(&mut self, t: u32, sent: &SentRoot) {
        self.trees[t as usize].root = *sent.digest();
        self.trees[t as usize].sent = sent.clone();
    }
    pub fn goes_on(&mut self, run: &crate::hash::modes::Digest) {
        self.run = *run;
    }
    pub fn salt_bytes(&self) -> usize {
        self.salt_bytes
    }
    pub fn adopt(&mut self, t: u32, from: &Tree) {
        let at = &mut self.trees[t as usize];
        assert!(
            from.parts.len() == at.parts.len(),
            "trees: a tree is adopted with all the oracle messages that lie in it"
        );
        assert!(
            !from.one_list && !at.one_list,
            "trees: a tree that holds the mask of one step is read in no other chain"
        );
        at.shape = from.shape.clone();
        at.root = from.root;
        at.sent = from.sent.clone();
        at.lists = from.lists.clone();
        at.positions = from.positions.clone();
    }
    pub fn count_opening(&mut self, st: &Statement, t: u32) {
        let tree = &mut self.trees[t as usize];
        let mut groups: Option<&Vec<GroupId>> = None;
        for o in &tree.parts {
            if st.oracle(*o).shape.answers == 0 {
                continue;
            }
            let mine = &st.oracle(*o).groups;
            assert!(
                groups.is_none() || groups.unwrap() == mine,
                "trees: oracle messages that share a leaf belong to different groups, so they are read at different lists"
            );
            groups = Some(mine);
        }
        assert!(
            !tree.one_list || groups.is_none() || groups.unwrap().len() <= 1,
            "trees: the mask of one step shares a leaf with an oracle message that is read at several lists"
        );
        assert!(
            !tree.one_list || tree.lists.get() == 0,
            "trees: a tree that holds the mask of one step is opened at a second list"
        );
        tree.lists.set(tree.lists.get() + 1);
    }
    pub fn trees(&self) -> usize {
        self.trees.len()
    }
    pub fn place(&self, o: OracleId) -> Place {
        assert!((o as usize) < self.place.len(), "trees: no such oracle message");
        self.place[o as usize]
    }

    /// `enter` (context.h:254-273): adds the notices to the statement and creates their trees.
    pub fn enter(
        &mut self,
        st: &mut Statement,
        sent: &[OracleNotice],
        ids: &mut Vec<OracleId>,
    ) -> u32 {
        let lay = lay_trees(st.codes(), sent, self.salt_bytes);
        let first = self.trees.len() as u32;
        for s in &lay.shapes {
            let mut shape = s.clone();
            shape.tree_number = self.trees.len() as u32;
            shape.run = self.run;
            shape.parameters = self.configuration;
            self.trees.push(Tree {
                shape,
                root: crate::hash::modes::Digest::zero(),
                sent: SentRoot::default(),
                parts: Vec::new(),
                one_list: false,
                lists: Rc::new(Cell::new(0)),
                positions: Rc::new(Cell::new(0)),
            });
        }
        ids.clear();
        for (i, n) in sent.iter().enumerate() {
            let o = st.sent(n.shape.clone());
            assert!(
                o as usize == self.place.len(),
                "trees: every oracle message enters the statement through this call"
            );
            let tree = first + lay.tree[i];
            self.place.push(Place { tree, part: lay.part[i] });
            self.trees[tree as usize].parts.push(o);
            if n.shape.answers == 0 {
                self.trees[tree as usize].one_list = true;
            }
            ids.push(o);
        }
        first
    }

    pub fn trees_of(&self, ids: &[OracleId]) -> Vec<u32> {
        let mut t: Vec<u32> = ids.iter().map(|o| self.place(*o).tree).collect();
        t.sort_unstable();
        t.dedup();
        t
    }
    pub fn list_for(&self, t: u32, at: &PositionList) -> PositionList {
        let log_n = self.trees[t as usize].shape.log_n;
        if log_n == at.log_n() {
            at.clone()
        } else {
            at.short_list(log_n)
        }
    }

    /// `sort_out` (context.h:291-316): the rows of `ids` from the opened columns.
    pub fn sort_out(
        &self,
        st: &Statement,
        ids: &[OracleId],
        at: &PositionList,
        trees: &[u32],
        opening: &[Opening],
        out: &mut Opened,
    ) {
        out.of = vec![vec![Column::default(); at.size()]; ids.len()];
        for (w, o) in ids.iter().enumerate() {
            let p = self.place(*o);
            let t = &self.trees[p.tree as usize];
            let j = trees.binary_search(&p.tree).unwrap();
            let own = self.list_for(p.tree, at);
            let s = &st.oracle(*o).shape;
            let mut main_skip = 0usize;
            let mut mask_skip = 0usize;
            for q in 0..p.part {
                main_skip += t.shape.main_symbols[q as usize];
                mask_skip += t.shape.mask_symbols[q as usize];
            }
            for i in 0..at.size() {
                let short = crate::code::short_position::short_position(at.log_n(), own.log_n(), at.at(i));
                let here = PositionList::index_in(own.all(), short);
                let col = &mut out.of[w][i];
                if s.main_rows > 0 {
                    let c = &opening[j as usize].main_column(here)[main_skip..];
                    for b in 0..s.main_rows {
                        col.main.push(if s.main_deg == 1 {
                            E([c[b], F::zero(), F::zero()])
                        } else {
                            E([c[3 * b], c[3 * b + 1], c[3 * b + 2]])
                        });
                    }
                }
                if s.mask_rows > 0 {
                    let c = &opening[j as usize].mask_column(here)[mask_skip..];
                    for b in 0..s.mask_rows {
                        col.mask.push(E([c[3 * b], c[3 * b + 1], c[3 * b + 2]]));
                    }
                }
            }
        }
    }

    pub fn whole_trees(&self, ids: &[OracleId]) -> bool {
        for t in self.trees_of(ids) {
            for o in &self.trees[t as usize].parts {
                if !ids.contains(o) {
                    return false;
                }
            }
        }
        true
    }
}

/// The verifier's context (`VerifierContext`, context.h:514-535).
pub struct VerifierContext<'x, 'a, 'd, 's> {
    pub st: Statement,
    pub ch: &'x mut VerifierRounds<'a, 'd, 's>,
    pub book: TreeBook,
    pub notes: Option<Vec<(String, E)>>,
}

impl<'x, 'a, 'd, 's> VerifierContext<'x, 'a, 'd, 's> {
    pub fn new(codes: &Public<Codes>, c: &'x mut VerifierRounds<'a, 'd, 's>) -> Self {
        let st = Statement::new(c.get(codes).clone());
        let book = TreeBook::new(c.plan().set.salt_bytes as usize, c.run(), c.configuration());
        let mut v = VerifierContext { st, ch: c, book, notes: None };
        v.st.has_no_engine();
        v
    }
    /// A context that continues on a later chain (`VerifierContext(VerifierContext&&, ...)`,
    /// context.h:530-534).
    pub fn goes_on<'y, 'b, 'e, 'f>(
        self,
        later: &'y mut VerifierRounds<'b, 'e, 'f>,
    ) -> VerifierContext<'y, 'b, 'e, 'f> {
        assert!(
            later.stands_on(self.ch),
            "context: the later chain's first query does not hold the earlier chain's seal"
        );
        assert!(
            later.plan().set.salt_bytes as usize == self.book.salt_bytes(),
            "context: the two chains' plans differ in the length of a salt"
        );
        let mut book = self.book;
        book.goes_on(later.run());
        let mut v = VerifierContext { st: self.st, ch: later, book, notes: None };
        v.st.has_no_engine();
        v
    }
    pub fn note(&mut self, what: &str, value: E) {
        if let Some(notes) = &mut self.notes {
            notes.push((String::from(what), value));
        }
    }
}

/// Reads the roots of all oracle messages of the present prover message (`receive_oracles`,
/// context.h:538-546).
pub fn receive_oracles(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    sent: &[OracleNotice],
    ids: &mut Vec<OracleId>,
) -> bool {
    let first = V.book.enter(&mut V.st, sent, ids);
    for t in first..V.book.trees() as u32 {
        let mut root = SentRoot::default();
        if !V.ch.recv_root(&mut root) {
            return false;
        }
        V.book.set_root(t, &root);
    }
    true
}

/// Reads the trees' openings and returns the symbols (`read_opened`, context.h:549-562).
pub fn read_opened(
    V: &mut VerifierContext<'_, '_, '_, '_>,
    ids: &[OracleId],
    at: &PositionList,
    out: &mut Opened,
    calls: &mut crate::hash::calls::HashCalls,
) -> bool {
    if !V.ch.ok() {
        return false;
    }
    assert!(
        V.book.whole_trees(ids),
        "open: an oracle message that shares a tree with those asked for is left out"
    );
    let trees = V.book.trees_of(ids);
    let mut opening = vec![Opening::default(); trees.len()];
    for (j, t) in trees.iter().enumerate() {
        V.book.count_opening(&V.st, *t);
        let own = V.book.list_for(*t, at);
        let sent = V.book.tree(*t).sent.clone();
        let shape = V.book.tree(*t).shape.clone();
        if !receive_opening(V.ch, &sent, &shape, &own, &mut opening[j], calls) {
            return false;
        }
    }
    V.book.sort_out(&V.st, ids, at, &trees, &opening, out);
    true
}


/// The sizes of the trees that hold some oracle messages (`tree_sizes`, context.h:150-165).
/// `last` is the caller's `OneList` counter: a tree with a message that has no answers may be read
/// at one list of positions only.
pub fn tree_sizes(
    codes: &Codes,
    sent: &[OracleNotice],
    last: &mut u64,
) -> alloc::vec::Vec<crate::numbers::blocks::TreeSize> {
    use crate::numbers::blocks::TreeSize;
    let lay = lay_trees(codes, sent, 0);
    let mut sizes = alloc::vec::Vec::new();
    for (i, t) in lay.shapes.iter().enumerate() {
        let mut z = TreeSize::default();
        for (o, n) in sent.iter().enumerate() {
            if lay.tree[o] as usize == i {
                if z.name.is_empty() {
                    z.name.push_str("tree of ");
                } else {
                    z.name.push_str("; ");
                }
                z.name.push_str(&n.shape.name);
            }
        }
        z.log_n = t.log_n;
        z.leaf_bytes = (t.main_width() + t.mask_width()) as u64 * 8; // F_BYTES
        for (o, n) in sent.iter().enumerate() {
            if lay.tree[o] as usize == i && n.shape.answers == 0 {
                z.one_list.mark(true, last);
            }
        }
        sizes.push(z);
    }
    sizes
}
