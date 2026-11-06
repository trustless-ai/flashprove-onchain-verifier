//! Merkle trees over digests, verifier side, ported from `blocks/tree/tree.h`.

use alloc::collections::btree_map::Entry;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use super::positions::PositionList;
use crate::hash::calls::HashCalls;
use crate::hash::domains::Domain;
use crate::hash::modes::{vertex, Digest, Tag};

/// A tree's depth and the parameters of its inner vertices (`TreeShape`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    pub log_n: u32,
    pub start: Digest,
    pub binding: bool,
}

impl TreeShape {
    pub fn plain(log_n: u32, start: Digest, binding: bool) -> Self {
        TreeShape { log_n, start, binding }
    }
    pub fn vertex_tag(&self) -> Tag {
        Tag::vertex(
            if self.binding { Domain::BindingNode } else { Domain::TreeNode },
            0,
            &self.start,
        )
    }
    pub fn valid(&self) -> bool {
        self.log_n <= 48 && self.start != Digest::zero()
    }
}

/// The vertex (depth, place) as one number (`tree_index`).
#[inline]
pub fn tree_index(depth: u32, place: u64) -> u64 {
    (1u64 << depth) + place
}

/// The values seen under one root across openings (`TreeValues`).
#[derive(Clone, Debug, Default)]
pub struct TreeValues {
    seen: BTreeMap<u64, Digest>,
    fresh: Vec<u64>,
    entered: u64,
    clashed: bool,
    clashed_before: bool,
    on_trial: bool,
}

impl TreeValues {
    /// Records a value; a vertex keeps its first. Returns false once two values clash.
    pub fn put(&mut self, depth: u32, place: u64, value: &Digest) -> bool {
        self.entered += 1;
        let key = tree_index(depth, place);
        // One tree search instead of a lookup followed by an insert on a miss.
        match self.seen.entry(key) {
            Entry::Occupied(o) => {
                if o.get() != value {
                    self.clashed = true;
                }
            }
            Entry::Vacant(v) => {
                v.insert(*value);
                if self.on_trial {
                    self.fresh.push(key);
                }
            }
        }
        !self.clashed
    }
    pub fn clashed(&self) -> bool {
        self.clashed
    }
    pub fn begin(&mut self) {
        assert!(!self.on_trial, "tree: two checks at once on one record");
        self.on_trial = true;
        self.clashed_before = self.clashed;
        self.fresh.clear();
    }
    pub fn keep(&mut self) {
        self.on_trial = false;
        self.fresh.clear();
    }
    pub fn take_back(&mut self) {
        for v in &self.fresh {
            self.seen.remove(v);
        }
        self.clashed = self.clashed_before;
        self.keep();
    }
    pub fn entered(&self) -> u64 {
        self.entered
    }
    pub fn vertices(&self) -> usize {
        self.seen.len()
    }
}

/// The walk from opened leaves to the root (`tree_walk`).
pub trait TreeSide {
    type Value: Clone + PartialEq;
    fn leaf(&mut self, i: usize) -> Self::Value;
    fn given(&mut self, depth: u32, place: u64) -> Option<Self::Value>;
    fn node(&mut self, depth: u32, place: u64, left: &Self::Value, right: &Self::Value) -> Self::Value;
}

pub fn tree_walk<S: TreeSide>(
    s: &TreeShape,
    list: &PositionList,
    side: &mut S,
    root: &mut S::Value,
) -> bool {
    assert!(s.valid(), "tree: not a shape");
    assert!(!list.is_empty() && list.log_n() == s.log_n, "tree: the list does not range over the tree's positions");
    let mut now: Vec<(u64, S::Value)> = (0..list.size()).map(|i| (list.at(i), side.leaf(i))).collect();
    let mut next: Vec<(u64, S::Value)> = Vec::with_capacity(now.len());
    let mut d = s.log_n;
    while d > 0 {
        next.clear();
        let mut v = 0usize;
        while v < now.len() {
            let place = now[v].0;
            let parent = place >> 1;
            if place & 1 == 0 && v + 1 < now.len() && now[v + 1].0 == place + 1 {
                let value = side.node(d - 1, parent, &now[v].1, &now[v + 1].1);
                next.push((parent, value));
                v += 2;
            } else {
                let other = match side.given(d, place ^ 1) {
                    Some(x) => x,
                    None => return false,
                };
                let value = if place & 1 != 0 {
                    side.node(d - 1, parent, &other, &now[v].1)
                } else {
                    side.node(d - 1, parent, &now[v].1, &other)
                };
                next.push((parent, value));
                v += 1;
            }
        }
        core::mem::swap(&mut now, &mut next);
        d -= 1;
    }
    assert!(now.len() == 1, "tree: a fault in tree_walk: it did not end in one vertex");
    *root = now[0].1.clone();
    true
}

/// The number of digests in an opening (`tree_given_count`).
pub fn tree_given_count(s: &TreeShape, list: &PositionList) -> usize {
    struct Count {
        n: usize,
    }
    impl TreeSide for Count {
        type Value = ();
        fn leaf(&mut self, _i: usize) -> () {}
        fn given(&mut self, _d: u32, _p: u64) -> Option<()> {
            self.n += 1;
            Some(())
        }
        fn node(&mut self, _d: u32, _p: u64, _l: &(), _r: &()) -> () {}
    }
    let mut side = Count { n: 0 };
    let mut root = ();
    let _ = tree_walk(s, list, &mut side, &mut root);
    side.n
}

/// The verifier's check of one opening (`tree_check`).
pub fn tree_check(
    root: &Digest,
    s: &TreeShape,
    list: &PositionList,
    leaves: &[Digest],
    given: &[Digest],
    seen: Option<&mut TreeValues>,
    mut clash: Option<&mut bool>,
    calls: &mut HashCalls,
) -> bool {
    if let Some(c) = clash.as_deref_mut() {
        *c = false;
    }
    if leaves.len() != list.size() {
        return false;
    }
    struct Check<'a, 'b> {
        shape: &'a TreeShape,
        tag: Tag,
        list: &'a PositionList,
        leaves: &'a [Digest],
        from_proof: &'a [Digest],
        seen: Option<&'b mut TreeValues>,
        used: usize,
        calls: &'b mut HashCalls,
    }
    impl<'a, 'b> Check<'a, 'b> {
        fn note(&mut self, d: u32, p: u64, v: &Digest) -> Digest {
            if d > 0 {
                if let Some(seen) = self.seen.as_deref_mut() {
                    seen.put(d, p, v);
                }
            }
            *v
        }
    }
    impl<'a, 'b> TreeSide for Check<'a, 'b> {
        type Value = Digest;
        fn leaf(&mut self, i: usize) -> Digest {
            let v = self.leaves[i];
            self.note(self.shape.log_n, self.list.at(i), &v)
        }
        fn given(&mut self, d: u32, p: u64) -> Option<Digest> {
            if self.used == self.from_proof.len() {
                return None;
            }
            let v = self.from_proof[self.used];
            self.used += 1;
            Some(self.note(d, p, &v))
        }
        fn node(&mut self, d: u32, p: u64, l: &Digest, r: &Digest) -> Digest {
            let v = vertex(&self.tag, l, r, self.calls);
            self.note(d, p, &v)
        }
    }
    let mut side = Check {
        shape: s,
        tag: s.vertex_tag(),
        list,
        leaves,
        from_proof: given,
        seen,
        used: 0,
        calls,
    };
    let mut computed = Digest::zero();
    let had_seen = side.seen.is_some();
    if let Some(seen) = side.seen.as_deref_mut() {
        seen.begin();
    }
    let led = tree_walk(s, list, &mut side, &mut computed) && side.used == given.len() && computed == *root;
    let clashed = side.seen.as_deref().map(|s| s.clashed()).unwrap_or(false);
    if let Some(c) = clash {
        *c = clashed;
    }
    if had_seen {
        let seen = side.seen.as_deref_mut().unwrap();
        if led && !clashed {
            seen.keep();
        } else {
            seen.take_back();
        }
    }
    led && !clashed
}
