//! The hash modes of `blocks/hash/hash.h`: `Digest`, `Tag`, the incremental `Hasher`, Merkle-tree
//! leaves and vertices, and a chain round's calls.
//!
//! Every hash here is BLAKE2b on a whole string. The string's first 16 bytes are the label:
//! `tag.word` then `index`, both little-endian. A start (BLAKE2b's salt and personalization) is
//! either in the tag (a tree's leaves and vertices) or passed with each call (a chain query, test
//! coins). The counter and flag are `Tweak`'s; `compress64` counts each call in `HashCalls::blk`.

use super::blake2b::{self, Start};
use super::calls::HashCalls;
use super::domains::{
    domain_has_start, domain_is_given_out, domain_is_leaf, domain_is_vertex, domain_start_in_tag,
    Domain,
};
use super::tweak::Tweak;
use crate::field::ext::{F, E};

pub const DIGEST_BYTES: usize = 32;
pub const LABEL_BYTES: usize = 16;
pub const LABEL_WORDS: usize = 2;
pub const SALT_FLOOR_BYTES: u64 = 40;
pub const SALT_MOST_BYTES: u64 = 64;
/// One compression's input (`HASH_BLOCK_BYTES`).
pub const BLOCK_BYTES: usize = 128;

/// A 256-bit digest, eight words of 32 bits (`blocks/hash/hash.h:44-62`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Digest {
    pub w: [u32; 8],
}

impl Digest {
    pub const fn zero() -> Self {
        Digest { w: [0; 8] }
    }

    pub fn from_bytes(b: &[u8; DIGEST_BYTES]) -> Self {
        let mut d = Digest::zero();
        for i in 0..8 {
            d.w[i] = b[4 * i] as u32
                | (b[4 * i + 1] as u32) << 8
                | (b[4 * i + 2] as u32) << 16
                | (b[4 * i + 3] as u32) << 24;
        }
        d
    }

    pub fn to_bytes(self) -> [u8; DIGEST_BYTES] {
        let mut b = [0u8; DIGEST_BYTES];
        for i in 0..DIGEST_BYTES {
            b[i] = (self.w[i / 4] >> (8 * (i % 4))) as u8;
        }
        b
    }
}

/// Compressions in a hash of `bytes` bytes of input, the label included (`mode_calls`).
pub const fn mode_calls(bytes: u64) -> u64 {
    (LABEL_BYTES as u64 + bytes + 4 * blake2b::BLKW as u64 - 1) / (4 * blake2b::BLKW as u64)
}

/// True for a salt of 40 to 64 bytes, a multiple of 8 (`salt_length_fits`).
pub const fn salt_length_fits(salt_bytes: u64) -> bool {
    salt_bytes >= SALT_FLOOR_BYTES && salt_bytes <= SALT_MOST_BYTES && salt_bytes % 8 == 0
}

/// The offset of a leaf's salt in the hashed string (`leaf_salt_at`).
pub const fn leaf_salt_at(symbols: u64, salt_bytes: u64) -> u64 {
    let at = LABEL_BYTES as u64 + 8 * symbols;
    if at % (4 * blake2b::BLKW as u64) + salt_bytes <= 4 * blake2b::BLKW as u64 {
        at
    } else {
        (at / (4 * blake2b::BLKW as u64) + 1) * (4 * blake2b::BLKW as u64)
    }
}

/// The length of a leaf's hashed string, the label included (`leaf_bytes`).
pub const fn leaf_bytes(symbols: u64, salt_bytes: u64) -> u64 {
    leaf_salt_at(symbols, salt_bytes) + salt_bytes
}

/// What the hashes of one use share (`TagT`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tag {
    pub word: u64,
    pub start: Start,
}

impl Tag {
    fn from_digest(d: &Digest) -> Start {
        Start { w: d.w }
    }

    /// The tag of a domain whose start is not in it (`TagT(Domain, tree)`).
    pub fn plain(d: Domain, tree: u64) -> Self {
        assert!(domain_is_given_out(d), "not a domain number of this format");
        assert!(
            tree < if d == Domain::ChainQuery { 1u64 << 48 } else { 1u64 << 16 },
            "a tree's number of 2^16 or more, or a chain's label of 2^48 or more"
        );
        assert!(!domain_start_in_tag(d), "the tag of a tree's hashes is made with their start");
        Tag {
            word: d as u64 | tree << 16,
            start: Start::default(),
        }
    }

    /// The tag of a tree's leaves (`TagT(Domain, tree, from, symbols, salt_bytes)`).
    pub fn leaf(d: Domain, tree: u32, from: &Digest, symbols: u64, salt_bytes: u64) -> Self {
        assert!(domain_is_leaf(d), "only leaves have a shape in their tag");
        assert!(tree < (1u32 << 16), "a tree's number is below 65536");
        assert!(symbols < (1u64 << 24), "a leaf has fewer than 2^24 symbols");
        assert!(salt_length_fits(salt_bytes), "a salt of 40 to 64 bytes, a multiple of 8");
        assert!(*from != Digest::zero(), "a start of zeros: it was not set");
        Tag {
            word: d as u64
                | (tree as u64) << 16
                | symbols << 32
                | (salt_bytes / 8) << 56,
            start: Self::from_digest(from),
        }
    }

    /// The tag of a tree's vertices (`TagT(Domain, tree, from)`).
    pub fn vertex(d: Domain, tree: u32, from: &Digest) -> Self {
        assert!(domain_start_in_tag(d), "only a tree's tags hold a start");
        assert!(!domain_is_leaf(d), "a leaf's tag is made with the leaves' shape");
        assert!(tree < (1u32 << 16), "a tree's number is below 65536");
        assert!(!domain_is_vertex(d) || tree == 0, "a vertex's hash holds nothing of its tree");
        assert!(*from != Digest::zero(), "a start of zeros: it was not set");
        Tag {
            word: d as u64 | (tree as u64) << 16,
            start: Self::from_digest(from),
        }
    }

    pub fn number(&self) -> Domain {
        Domain::from_word((self.word & 0xFFFF) as u32)
    }

    pub fn symbols(&self) -> u64 {
        (self.word >> 32) & 0xFF_FFFF
    }

    pub fn salt_bytes(&self) -> u64 {
        8 * (self.word >> 56)
    }
}

#[inline]
fn load64(p: &[u8]) -> u64 {
    let b: [u8; 8] = p[..8].try_into().unwrap();
    u64::from_le_bytes(b)
}

/// The hash of one string, fed piece by piece (`HasherT`).
pub struct Hasher<'a> {
    h: [u64; 8],
    t: u64,
    leaf: u64,
    buf: [u8; BLOCK_BYTES],
    buflen: u32,
    f: u32,
    calls: &'a mut HashCalls,
}

const MOST_BYTES: u64 = (1u64 << 32) - BLOCK_BYTES as u64;

impl<'a> Hasher<'a> {
    /// Begins `H(tag, index, start; bytes)` whose start is the tag's own.
    pub fn new(tag: &Tag, index: u64, calls: &'a mut HashCalls) -> Self {
        assert!(
            !(domain_has_start(tag.number()) && !domain_start_in_tag(tag.number())),
            "a hash under this number starts from a digest"
        );
        Self::init(tag, index, tag.start, DIGEST_BYTES as u32, calls)
    }

    /// The same under a domain whose start comes with each hash; BLAKE2b's digest is 64 bytes for
    /// `CHAIN_QUERY`.
    pub fn new_with_start(
        tag: &Tag,
        index: u64,
        start: &Digest,
        calls: &'a mut HashCalls,
    ) -> Self {
        assert!(
            domain_has_start(tag.number()) && !domain_start_in_tag(tag.number()),
            "a hash under this number takes no start of its own"
        );
        let s = Start { w: start.w };
        let digest_bytes = if tag.number() == Domain::ChainQuery {
            64
        } else {
            DIGEST_BYTES as u32
        };
        Self::init(tag, index, s, digest_bytes, calls)
    }

    fn init(
        tag: &Tag,
        index: u64,
        start: Start,
        digest_bytes: u32,
        calls: &'a mut HashCalls,
    ) -> Self {
        assert!(index < (1u64 << 63), "a hash's index must be below 2^63");
        let leaf = if domain_is_leaf(tag.number()) {
            leaf_bytes(tag.symbols(), tag.salt_bytes())
        } else {
            0
        };
        let mut s = Hasher {
            h: [0u64; 8],
            t: 0,
            leaf,
            buf: [0u8; BLOCK_BYTES],
            buflen: 0,
            f: 0,
            calls,
        };
        s.clear_buf();
        blake2b::begin64(&mut s.h, &start, digest_bytes);
        s.push_u64(tag.word);
        s.push_u64(index);
        s
    }

    /// Appends `x`'s four bytes, the lowest first (`push_u32`).
    pub fn push_u32(&mut self, x: u32) {
        let b = x.to_le_bytes();
        self.push(&b);
    }

    /// Appends `x`'s eight bytes, the lowest first (`push_u64`).
    pub fn push_u64(&mut self, x: u64) {
        let b = x.to_le_bytes();
        self.push(&b);
    }

    /// Appends an F as its eight little-endian bytes (`push(F)`).
    pub fn push_f(&mut self, x: F) {
        self.push_u64(x.0);
    }

    /// Appends an E as its three coordinates, c[0] first (`push(E)`).
    pub fn push_e(&mut self, x: E) {
        for i in 0..3 {
            self.push_u64(x.0[i].0);
        }
    }

    /// Appends a digest as its eight words (`push(Digest)`).
    pub fn push_digest(&mut self, d: &Digest) {
        for w in d.w {
            self.push_u32(w);
        }
    }

    /// Appends bytes (`push`). A buffer that has just become full is not compressed yet.
    pub fn push(&mut self, data: &[u8]) {
        if data.is_empty() {
            return;
        }
        assert!(self.f == 0, "a hash that was finished takes no more input");
        assert!(
            data.len() as u64 <= MOST_BYTES - (self.t + self.buflen as u64),
            "a hash takes at most 2^32 bytes less one block"
        );
        let mut pos = 0usize;
        let left = self.buflen as usize;
        let fill = BLOCK_BYTES - left;
        if data.len() > fill {
            self.buflen = 0;
            self.buf[left..left + fill].copy_from_slice(&data[..fill]);
            self.increment_counter(BLOCK_BYTES as u64);
            let tweak = blake2b::step((self.t / BLOCK_BYTES as u64 - 1) as u32);
            let block = self.buf;
            self.compress_block(&block, &tweak);
            self.clear_buf();
            pos = fill;
            while data.len() - pos > BLOCK_BYTES {
                self.increment_counter(BLOCK_BYTES as u64);
                let tweak = blake2b::step((self.t / BLOCK_BYTES as u64 - 1) as u32);
                let mut block = [0u8; BLOCK_BYTES];
                block.copy_from_slice(&data[pos..pos + BLOCK_BYTES]);
                self.compress_block(&block, &tweak);
                pos += BLOCK_BYTES;
            }
        }
        let rem = data.len() - pos;
        let at = self.buflen as usize;
        self.buf[at..at + rem].copy_from_slice(&data[pos..]);
        self.buflen += rem as u32;
    }

    /// The number of bytes pushed so far; the label is not counted (`bytes`).
    pub fn bytes(&self) -> u64 {
        self.t + self.buflen as u64 - LABEL_BYTES as u64
    }

    /// Compresses the last block and returns the digest's first 32 bytes (`finish`).
    pub fn finish(&mut self) -> Digest {
        assert!(
            self.leaf == 0 || self.t + self.buflen as u64 == self.leaf,
            "a leaf was not fed what its tag says"
        );
        self.increment_counter(self.buflen as u64);
        self.set_lastblock();
        let bytes = self.t as u32;
        let block = self.buf;
        self.compress_block(&block, &blake2b::last(bytes));
        self.clear_buf();
        self.buflen = 0;
        let mut d = Digest::zero();
        for i in 0..4 {
            d.w[2 * i] = self.h[i] as u32;
            d.w[2 * i + 1] = (self.h[i] >> 32) as u32;
        }
        d
    }

    /// Hands over the chaining value and the last block without compressing it
    /// (`before_nonce`).
    pub fn before_nonce(&mut self) -> ChainPrefix {
        self.set_lastblock();
        assert!(
            self.bytes() > 0 && self.buflen % 8 == 0,
            "a round's message is a multiple of 8 bytes and ends with the call's word"
        );
        let last = load64(&self.buf[self.buflen as usize - 8..]);
        assert!(
            last >> 16 == 0,
            "the last word of a round's message must leave its bits from 16 up to the call's number"
        );
        let mut out = ChainPrefix::default();
        out.steps = (self.t / BLOCK_BYTES as u64) as u32;
        out.fill = self.buflen;
        for i in 0..16 {
            let w = load64(&self.buf[8 * i..]);
            out.block[2 * i] = w as u32;
            out.block[2 * i + 1] = (w >> 32) as u32;
        }
        for i in 0..8 {
            out.cv[2 * i] = self.h[i] as u32;
            out.cv[2 * i + 1] = (self.h[i] >> 32) as u32;
        }
        self.increment_counter(self.buflen as u64);
        self.clear_buf();
        self.buflen = 0;
        out
    }

    fn clear_buf(&mut self) {
        self.buf = [0u8; BLOCK_BYTES];
    }

    fn set_lastblock(&mut self) {
        assert!(self.f == 0, "a hash is finished once");
        self.f = 1;
    }

    fn increment_counter(&mut self, inc: u64) {
        self.t = self.t.wrapping_add(inc);
    }

    fn compress_block(&mut self, block: &[u8; BLOCK_BYTES], tweak: &Tweak) {
        let mut m = [0u64; 16];
        for i in 0..16 {
            m[i] = load64(&block[8 * i..]);
        }
        let h = &mut self.h;
        let calls = &mut *self.calls;
        blake2b::compress64(h, &m, tweak, calls);
    }
}

/// The hash state that the calls of one round share (`ChainPrefixT`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ChainPrefix {
    pub cv: [u32; blake2b::CVW],
    pub block: [u32; blake2b::BLKW],
    pub fill: u32,
    pub steps: u32,
}

/// The 64 bytes of one call, as words of 8 bytes (`ChainCall`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ChainCall {
    pub w: [u64; 8],
}

/// One half of a call's answer (`chain_block`).
pub fn chain_block(c: &ChainCall, half: usize) -> Digest {
    let mut d = Digest::zero();
    for i in 0..4 {
        d.w[2 * i] = c.w[4 * half + i] as u32;
        d.w[2 * i + 1] = (c.w[4 * half + i] >> 32) as u32;
    }
    d
}

/// The label and two digests in one compression (`two_digests`).
pub fn two_digests(
    tag: &Tag,
    index: u64,
    left: &Digest,
    right: &Digest,
    calls: &mut HashCalls,
) -> Digest {
    assert!(
        !(domain_has_start(tag.number()) && !domain_start_in_tag(tag.number())),
        "a hash under this number starts from a digest of its own"
    );
    assert!(index < (1u64 << 63), "a hash's index must be below 2^63");
    let mut cv = [0u32; blake2b::CVW];
    let mut m = [0u32; blake2b::BLKW];
    blake2b::begin(&mut cv, &tag.start, DIGEST_BYTES as u32);
    m[0] = tag.word as u32;
    m[1] = (tag.word >> 32) as u32;
    m[2] = index as u32;
    m[3] = (index >> 32) as u32;
    m[4..12].copy_from_slice(&left.w);
    m[12..20].copy_from_slice(&right.w);
    blake2b::compress(&mut cv, &m, &blake2b::last((LABEL_BYTES + 64) as u32), calls);
    let mut d = Digest::zero();
    d.w.copy_from_slice(&cv[..8]);
    d
}

/// A non-vertex hash of two digests with an index (`node`).
pub fn node(tag: &Tag, index: u64, left: &Digest, right: &Digest, calls: &mut HashCalls) -> Digest {
    assert!(!domain_is_vertex(tag.number()), "a tree's vertex is made by vertex()");
    two_digests(tag, index, left, right, calls)
}

/// A Merkle-tree vertex (`vertex`).
pub fn vertex(tag: &Tag, left: &Digest, right: &Digest, calls: &mut HashCalls) -> Digest {
    assert!(domain_is_vertex(tag.number()), "a vertex is hashed under a number of vertices");
    two_digests(tag, 0, left, right, calls)
}

/// A vertex with the start given directly (`vertex(left, right, start)`).
pub fn vertex_with_start(
    left: &Digest,
    right: &Digest,
    start: &Digest,
    calls: &mut HashCalls,
) -> Digest {
    let tag = Tag::vertex(Domain::TreeNode, 0, start);
    two_digests(&tag, 0, left, right, calls)
}

/// A run's value (`run_value`).
pub fn run_value(label: u64, parameters: &Digest, random_bytes: &Digest, calls: &mut HashCalls) -> Digest {
    // The label is the index, not the tag's tree (blocks/hash/hash.h: `node(Domain::RUN, label, ..)`).
    node(&Tag::plain(Domain::Run, 0), label, parameters, random_bytes, calls)
}

/// The end of both forms of `leaf()` (`leaf_end`).
pub fn leaf_end(
    h: &mut Hasher<'_>,
    tag: &Tag,
    count: usize,
    salt: &[u8],
) -> Digest {
    assert!(domain_is_leaf(tag.number()), "a leaf hashes under a leaf's number");
    assert!(count as u64 == tag.symbols(), "a leaf of another shape than its tag says");
    assert!(salt.len() as u64 == tag.salt_bytes(), "a leaf of another shape than its tag says");
    let mut at = LABEL_BYTES as u64 + 8 * count as u64;
    let end = leaf_salt_at(count as u64, salt.len() as u64);
    while at < end {
        h.push_u64(0);
        at += 8;
    }
    h.push(salt);
    h.finish()
}

/// A leaf whose content is `count` base-field symbols (`leaf`).
pub fn leaf(
    tag: &Tag,
    index: u64,
    symbols: &[F],
    count: usize,
    salt: &[u8],
    calls: &mut HashCalls,
) -> Digest {
    let mut h = Hasher::new(tag, index, calls);
    for x in symbols.iter().take(count) {
        h.push_f(*x);
    }
    leaf_end(&mut h, tag, count, salt)
}

/// A leaf whose content is one digest (`leaf(Digest)`).
pub fn leaf_digest(
    tag: &Tag,
    index: u64,
    content: &Digest,
    salt: &[u8],
    calls: &mut HashCalls,
) -> Digest {
    let mut h = Hasher::new(tag, index, calls);
    h.push_digest(content);
    leaf_end(&mut h, tag, 4, salt)
}

/// Pushes the label and begins a chain round (`ChainAbsorbT`).
pub fn chain_absorb<'a>(
    rho_prev: &Digest,
    round: u64,
    chain: u64,
    calls: &'a mut HashCalls,
) -> Hasher<'a> {
    Hasher::new_with_start(&Tag::plain(Domain::ChainQuery, chain), round, rho_prev, calls)
}

/// Call `j` of a round (`chain_call`).
pub fn chain_call(p: &ChainPrefix, nonce: u64, j: u64, calls: &mut HashCalls) -> ChainCall {
    assert!(j < (1u64 << 48), "a call's number is below 2^48");
    let at = (p.fill / 4) as u32;
    let mut cv = p.cv;
    let mut m = p.block;
    for i in 0..blake2b::BLKW {
        let iu = i as u32;
        m[i] = if iu == at {
            nonce as u32
        } else if iu == at + 1 {
            (nonce >> 32) as u32
        } else if iu + 2 == at {
            p.block[i] | ((j << 16) as u32)
        } else if iu + 1 == at {
            p.block[i] | ((j >> 16) as u32)
        } else {
            p.block[i]
        };
    }
    let bytes = p
        .steps
        .wrapping_mul(4 * blake2b::BLKW as u32)
        .wrapping_add(p.fill)
        .wrapping_add(8);
    if at == blake2b::BLKW as u32 {
        blake2b::compress(&mut cv, &m, &blake2b::step(p.steps), calls);
        m = [0u32; blake2b::BLKW];
        m[0] = nonce as u32;
        m[1] = (nonce >> 32) as u32;
    }
    blake2b::compress(&mut cv, &m, &blake2b::last(bytes), calls);
    let mut c = ChainCall::default();
    for i in 0..8 {
        c.w[i] = cv[2 * i] as u64 | (cv[2 * i + 1] as u64) << 32;
    }
    c
}

/// The same as `chain_absorb` + `chain_call` on `CELLS` message words, every index fixed
/// (`chain_call_cells`).
pub fn chain_call_cells<const CELLS: usize>(
    rho_prev: &Digest,
    round: u64,
    cells: &[u64; CELLS],
    nonce: u64,
    j: u64,
    chain: u64,
    calls: &mut HashCalls,
) -> ChainCall {
    assert!(CELLS >= 1, "the message ends with the word that takes the call's number");
    assert!(
        cells[CELLS - 1] >> 16 == 0 && j < (1u64 << 48),
        "the last word of a round's message must leave its bits from 16 up"
    );
    assert!(round < (1u64 << 63), "a hash's index must be below 2^63");
    const PER: usize = blake2b::BLKW / 2;
    let all = LABEL_WORDS + CELLS + 1;
    let steps = (all - 1) / PER;
    let tag_word = Domain::ChainQuery as u64 | chain << 16;
    let start = Start { w: rho_prev.w };
    let mut h = [0u64; 8];
    let mut m = [0u64; PER];
    blake2b::begin64(&mut h, &start, 2 * DIGEST_BYTES as u32);
    for s in 0..=steps {
        for i in 0..PER {
            let cell = (s * PER + i) as i64 - LABEL_WORDS as i64;
            m[i] = if cell == -2 {
                tag_word
            } else if cell == -1 {
                round
            } else if cell + 1 < CELLS as i64 {
                cells[if cell >= 0 && cell + 1 < CELLS as i64 { cell as usize } else { 0 }]
            } else if cell + 1 == CELLS as i64 {
                cells[CELLS - 1] | j << 16
            } else if cell == CELLS as i64 {
                nonce
            } else {
                0
            };
        }
        if s < steps {
            blake2b::compress64(&mut h, &m, &blake2b::step(s as u32), calls);
        }
    }
    blake2b::compress64(&mut h, &m, &blake2b::last((8 * all) as u32), calls);
    ChainCall { w: h }
}

/// Whether the low `bits` bits of a word are zero (`work_test`).
pub fn work_test(word: u64, bits: u32) -> bool {
    assert!(bits <= 64, "the work test takes 0 to 64 bits");
    bits == 0 || (word << (64 - bits)) == 0
}

/// The work test of a round, on call 0 (`chain_work_passes`).
pub fn chain_work_passes(p: &ChainPrefix, nonce: u64, bits: u32, calls: &mut HashCalls) -> bool {
    work_test(chain_call(p, nonce, 0, calls).w[0], bits)
}

/// `H(TEST_COINS, counter, start = seed; nothing)` (`test_coins`).
pub fn test_coins(seed: &Digest, counter: u64, calls: &mut HashCalls) -> Digest {
    let tag = Tag::plain(Domain::TestCoins, 0);
    let mut h = Hasher::new_with_start(&tag, counter, seed, calls);
    h.finish()
}

