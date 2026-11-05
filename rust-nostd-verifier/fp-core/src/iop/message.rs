//! Byte encoding of proofs and hashed public data, ported from `blocks/iop/message.h`.
//!
//! A `Writer` appends typed items; a `Reader` reads them in the same order. An item carries no
//! length or type: the reader knows what follows from public data. Integers are little-endian. A
//! read fails if it passes the end or meets an `F`/`E` coordinate not below the modulus, and later
//! reads fail too. Only `at_end()` detects leftover bytes.

use alloc::string::String;
use alloc::vec::Vec;

use crate::field::ext::{F, E};
use crate::hash::modes::{Digest, DIGEST_BYTES};

/// One listed item (`Writer::Item`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Item {
    pub at: usize,
    pub bytes: usize,
    pub kind: u8, // b'F', b'E', b'D', b'W' or b'B'
}

/// A mark in a `Writer`'s list (`Writer::Mark`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mark {
    pub at: usize,
    pub words: String,
}

/// Appends typed items; `listed` records offsets and kinds for planning tools.
#[derive(Clone, Debug, Default)]
pub struct Writer {
    buf: Vec<u8>,
    listed: bool,
    items: Vec<Item>,
    marks: Vec<Mark>,
}

impl Writer {
    pub fn put_bytes(&mut self, p: &[u8]) {
        self.append(b'B', p);
    }

    pub fn put_u64(&mut self, x: u64) {
        self.append(b'W', &x.to_le_bytes());
    }

    pub fn put_f(&mut self, x: F) {
        self.append(b'F', &x.to_bytes());
    }

    pub fn put_e(&mut self, x: E) {
        self.append(b'E', &x.to_bytes());
    }

    pub fn put_digest(&mut self, d: &Digest) {
        self.append(b'D', &d.to_bytes());
    }

    pub fn size(&self) -> usize {
        self.buf.len()
    }

    pub fn data(&self) -> &[u8] {
        &self.buf
    }

    pub fn bytes(&self) -> &[u8] {
        &self.buf
    }

    pub fn clear(&mut self) {
        self.buf.clear();
        self.items.clear();
        self.marks.clear();
    }

    pub fn keep_list(&mut self) {
        self.listed = true;
    }

    /// Appends another writer's bytes, and its listed items and marks shifted.
    pub fn append_writer(&mut self, other: &Writer) {
        let moved = self.buf.len();
        if self.listed {
            for i in &other.items {
                self.items.push(Item { at: i.at + moved, bytes: i.bytes, kind: i.kind });
            }
            for m in &other.marks {
                self.marks.push(Mark { at: m.at + moved, words: m.words.clone() });
            }
            if !other.listed && other.size() != 0 {
                self.items.push(Item { at: moved, bytes: other.size(), kind: b'B' });
            }
        }
        self.buf.extend_from_slice(&other.buf);
    }

    pub fn mark(&mut self, words: &str) {
        if self.listed {
            self.marks.push(Mark { at: self.buf.len(), words: String::from(words) });
        }
    }

    pub fn items(&self) -> &[Item] {
        &self.items
    }

    pub fn marks(&self) -> &[Mark] {
        &self.marks
    }

    fn append(&mut self, kind: u8, p: &[u8]) {
        if self.listed {
            self.items.push(Item { at: self.buf.len(), bytes: p.len(), kind });
        }
        self.buf.extend_from_slice(p);
    }
}

/// Reads typed items from a byte slice (`Reader`).
#[derive(Clone, Debug)]
pub struct Reader<'a> {
    p: &'a [u8],
    at: usize,
    ok: bool,
}

impl<'a> Reader<'a> {
    pub fn new(p: &'a [u8]) -> Self {
        Reader { p, at: 0, ok: true }
    }

    pub fn ok(&self) -> bool {
        self.ok
    }

    pub fn at_end(&self) -> bool {
        self.ok && self.at == self.p.len()
    }

    pub fn refuse(&mut self) {
        self.ok = false;
    }

    /// The next `n` bytes, or `None` on failure.
    pub fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if !self.ok || self.p.len() - self.at < n {
            self.ok = false;
            return None;
        }
        let q = &self.p[self.at..self.at + n];
        self.at += n;
        Some(q)
    }

    pub fn get_u64(&mut self) -> Option<u64> {
        let q = self.take(8)?;
        Some(u64::from_le_bytes(q.try_into().unwrap()))
    }

    pub fn get_f(&mut self) -> Option<F> {
        let q = self.take(8)?;
        let b: &[u8; 8] = q.try_into().unwrap();
        let v = F::from_bytes(b);
        if v.is_none() {
            self.ok = false;
        }
        v
    }

    pub fn get_e(&mut self) -> Option<E> {
        let q = self.take(24)?;
        let b: &[u8; 24] = q.try_into().unwrap();
        let v = E::from_bytes(b);
        if v.is_none() {
            self.ok = false;
        }
        v
    }

    pub fn get_digest(&mut self) -> Option<Digest> {
        let q = self.take(DIGEST_BYTES)?;
        Some(Digest::from_bytes(q.try_into().unwrap()))
    }
}
