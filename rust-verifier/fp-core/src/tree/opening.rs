//! Oracle-tree leaves, openings and their verifier checks, ported from
//! `blocks/tree/opening.h` (verifier side; the prover's `OracleTree` is not ported).

use alloc::vec;
use alloc::vec::Vec;

use super::positions::PositionList;
use super::tree::{tree_check, tree_given_count, tree_index, TreeShape, TreeValues};
use crate::chain::rounds::{SentRoot, VerifierRounds};
use crate::field::ext::F;
use crate::hash::calls::HashCalls;
use crate::hash::domains::Domain;
use crate::hash::modes::{leaf, Digest, Tag, DIGEST_BYTES, SALT_FLOOR_BYTES, SALT_MOST_BYTES};
use crate::iop::message::{Reader, Writer};

/// How the rows of one tree are shaped (`OracleTreeShape`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OracleTreeShape {
    pub log_n: u32,
    pub log_n_zk: u32,
    pub main_symbols: Vec<usize>,
    pub mask_symbols: Vec<usize>,
    pub tree_number: u32,
    pub salt_bytes: usize,
    pub stored: bool,
    pub run: Digest,
    pub parameters: Digest,
}

impl OracleTreeShape {
    pub fn sum(v: &[usize]) -> usize {
        v.iter().sum()
    }
    pub fn main_width(&self) -> usize {
        Self::sum(&self.main_symbols)
    }
    pub fn mask_width(&self) -> usize {
        Self::sum(&self.mask_symbols)
    }
    pub fn has_main(&self) -> bool {
        self.main_width() > 0
    }
    pub fn has_mask(&self) -> bool {
        self.mask_width() > 0
    }
    pub fn width(&self) -> usize {
        self.main_width() + self.mask_width()
    }
    pub fn tree(&self) -> TreeShape {
        TreeShape::plain(self.log_n, self.parameters, false)
    }
    pub fn valid(&self) -> bool {
        if self.main_symbols.len() != self.mask_symbols.len() {
            return false;
        }
        if !self.has_main() && !self.has_mask() {
            return false;
        }
        if self.has_mask() && self.log_n_zk > self.log_n {
            return false;
        }
        if !self.has_main() && self.log_n != self.log_n_zk {
            return false;
        }
        if !(self.salt_bytes as u64 >= SALT_FLOOR_BYTES
            && self.salt_bytes as u64 <= SALT_MOST_BYTES
            && self.salt_bytes % 8 == 0)
        {
            return false;
        }
        if (self.width() as u64) >> 24 != 0 {
            return false;
        }
        if self.parameters == Digest::zero() || (!self.stored && self.run == Digest::zero()) {
            return false;
        }
        self.tree_number < (1u32 << 16) && self.tree().valid()
    }
}

/// The tag and vertex number that a tree's leaves share (`LeafHash`).
#[derive(Clone, Copy, Debug)]
pub struct LeafHash {
    pub tag: Tag,
    pub log_n: u32,
    pub salt_bytes: usize,
}

impl LeafHash {
    pub fn new(s: &OracleTreeShape) -> Self {
        LeafHash {
            tag: Tag::leaf(
                if s.stored { Domain::LeafStoredMain } else { Domain::LeafMain },
                s.tree_number,
                if s.stored { &s.parameters } else { &s.run },
                s.width() as u64,
                s.salt_bytes as u64,
            ),
            log_n: s.log_n,
            salt_bytes: s.salt_bytes,
        }
    }
    pub fn hash(
        &self,
        x: u64,
        column: &[F],
        count: usize,
        salt: &[u8],
        calls: &mut HashCalls,
    ) -> Digest {
        leaf(
            &self.tag,
            tree_index(self.log_n, x),
            column,
            count,
            &salt[..self.salt_bytes],
            calls,
        )
    }
}

pub fn oracle_leaf(
    s: &OracleTreeShape,
    x: u64,
    column: &[F],
    count: usize,
    salt: &[u8],
    calls: &mut HashCalls,
) -> Digest {
    LeafHash::new(s).hash(x, column, count, salt, calls)
}

/// An opening at a list of positions (`Opening`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Opening {
    pub columns: Vec<F>,
    pub salts: Vec<u8>,
    pub given: Vec<Digest>,
    pub main_width: usize,
    pub mask_width: usize,
}

impl Opening {
    pub fn column(&self, i: usize) -> &[F] {
        let w = self.main_width + self.mask_width;
        &self.columns[i * w..i * w + w]
    }
    pub fn main_column(&self, i: usize) -> &[F] {
        &self.column(i)[..self.main_width]
    }
    pub fn mask_column(&self, i: usize) -> &[F] {
        &self.column(i)[self.main_width..]
    }
}

pub fn opening_given(s: &OracleTreeShape, list: &PositionList) -> usize {
    assert!(s.valid(), "opening: not a shape");
    assert!(!list.is_empty() && list.log_n() == s.log_n, "opening: the list does not range over the tree's positions");
    tree_given_count(&s.tree(), list)
}

pub fn opening_bytes(s: &OracleTreeShape, list: &PositionList) -> usize {
    list.size() * (s.width() * 8 + s.salt_bytes) + opening_given(s, list) * DIGEST_BYTES
}

pub fn write_opening(
    w: &mut Writer,
    s: &OracleTreeShape,
    list: &PositionList,
    o: &Opening,
) {
    assert!(
        o.given.len() == opening_given(s, list)
            && o.columns.len() == list.size() * s.width()
            && o.salts.len() == list.size() * s.salt_bytes,
        "opening: its pieces have not the sizes that shape and list ask for"
    );
    for i in 0..list.size() {
        for j in 0..s.width() {
            w.put_f(o.columns[i * s.width() + j]);
        }
        w.put_bytes(&o.salts[i * s.salt_bytes..(i + 1) * s.salt_bytes]);
    }
    for d in &o.given {
        w.put_digest(d);
    }
}

/// Reads an opening; false if bytes are missing or a symbol is not canonical (`read_opening`).
pub fn read_opening(
    r: &mut Reader<'_>,
    s: &OracleTreeShape,
    list: &PositionList,
    o: &mut Opening,
) -> bool {
    *o = Opening::default();
    o.given = vec![Digest::zero(); opening_given(s, list)];
    o.main_width = s.main_width();
    o.mask_width = s.mask_width();
    o.columns = vec![F::zero(); list.size() * s.width()];
    o.salts = vec![0u8; list.size() * s.salt_bytes];
    if !r.ok() {
        return false;
    }
    for i in 0..list.size() {
        for j in 0..s.width() {
            match r.get_f() {
                Some(x) => o.columns[i * s.width() + j] = x,
                None => return false,
            }
        }
        match r.take(s.salt_bytes) {
            Some(q) => o.salts[i * s.salt_bytes..(i + 1) * s.salt_bytes].copy_from_slice(q),
            None => return false,
        }
    }
    for d in &mut o.given {
        match r.get_digest() {
            Some(x) => *d = x,
            None => return false,
        }
    }
    true
}

/// Hashes the opened columns and recomputes the root (`check_opening`).
pub fn check_opening(
    root: &Digest,
    s: &OracleTreeShape,
    list: &PositionList,
    o: &Opening,
    seen: Option<&mut TreeValues>,
    mut clash: Option<&mut bool>,
    calls: &mut HashCalls,
) -> bool {
    if let Some(c) = clash.as_deref_mut() {
        *c = false;
    }
    let _ = opening_given(s, list);
    if o.columns.len() != list.size() * s.width() || o.salts.len() != list.size() * s.salt_bytes {
        return false;
    }
    let lh = LeafHash::new(s);
    let mut leaves = vec![Digest::zero(); list.size()];
    for i in 0..list.size() {
        let salt_at = i * s.salt_bytes;
        leaves[i] = lh.hash(
            list.at(i),
            &o.columns[i * s.width()..(i + 1) * s.width()],
            s.width(),
            &o.salts[salt_at..salt_at + s.salt_bytes],
            calls,
        );
    }
    tree_check(root, &s.tree(), list, &leaves, &o.given, seen, clash, calls)
}

/// The verifier's entire step: reads an opening from the proof and checks it (`receive_opening`).
pub fn receive_opening(
    ch: &mut VerifierRounds<'_, '_, '_>,
    sent: &SentRoot,
    s: &OracleTreeShape,
    list: &PositionList,
    o: &mut Opening,
    calls: &mut HashCalls,
) -> bool {
    let root = *sent.digest();
    assert!(
        s.salt_bytes == ch.plan().set.salt_bytes as usize,
        "opening: the shape's salt has not the length that the chain's plan says"
    );
    assert!(
        s.parameters == *ch.configuration(),
        "opening: the shape's vertices do not start from the chain's configuration"
    );
    assert!(
        !ch.ok() || ch.drew(list),
        "opening: a list of positions that neither this chain nor one that it follows has drawn"
    );
    assert!(
        !ch.ok() || ch.received(sent),
        "opening: a root that neither this chain nor one that it follows has received"
    );
    assert!(
        !ch.ok() || (!s.stored && s.run == *sent.run() && s.parameters == *sent.configuration()),
        "opening: the shape's hashes do not start from the values of the chain that received the root"
    );
    if !read_opening(ch.file_only(), s, list, o) {
        ch.refuse_what_was_read("an opening is cut short or holds a symbol that is not in canonical form");
        return false;
    }
    let mut clash = false;
    let ok = {
        let seen = ch.session().record(&root);
        check_opening(&root, s, list, o, Some(seen), Some(&mut clash), calls)
    };
    if !ok {
        ch.refuse(if clash {
            "a vertex of a tree gets two values under one root"
        } else {
            "an opening does not lead to its root"
        });
        return false;
    }
    true
}
