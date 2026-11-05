//! Mask entries and their ledgers, ported from `blocks/iop/mask.h` (lines 1-147).
//!
//! A `MaskSlot` names one entry of an oracle message's mask rows and cannot be copied (Rust move
//! semantics). A `SampleReceipt` states that the message's out-of-domain sample was answered; it
//! builds one `MaskLedger`, which gives out each free entry once, in increasing order. `SendAccess`
//! is the C++ pass-key: outside this crate only `receipt_for_a_test` makes a receipt, and the ported
//! SEND block will be the production source.

use alloc::vec::Vec;

/// Identifies mask entry `index()` of oracle message `oracle()` (`MaskSlot`, mask.h:34-58). A value
/// of this type is moved into the claim that uses it; there is no copy.
#[derive(Debug, PartialEq, Eq)]
pub struct MaskSlot {
    oracle: u32,
    index: u32,
}

impl MaskSlot {
    pub fn oracle(&self) -> u32 {
        self.oracle
    }
    pub fn index(&self) -> u32 {
        self.index
    }
    fn new(oracle: u32, index: u32) -> Self {
        MaskSlot { oracle, index }
    }
}

/// `coeff * (the entry)` (`MaskTerm`, mask.h:61-65). K is the challenge field.
#[derive(Debug)]
pub struct MaskTerm<K> {
    pub slot: MaskSlot,
    pub coeff: K,
}

/// The C++ `SendAccess` pass-key (mask.h:77). A production send block constructs it inside the
/// crate; tests use `receipt_for_a_test`, as `blocks/iop/tests/toy_support.h` defines its own.
pub struct SendAccess;

/// States that a sample was answered and that `count` entries of its mask rows, from `first` on,
/// are free (`SampleReceipt`, mask.h:78-100). One receipt makes one ledger.
#[derive(Debug)]
pub struct SampleReceipt {
    oracle: u32,
    first: u32,
    count: u32,
    rows: u32,
    log_rows: u32,
    full: bool,
}

impl SampleReceipt {
    pub(crate) fn new(
        _: &SendAccess,
        oracle: u32,
        first: u32,
        count: u32,
        rows: u32,
        log_rows: u32,
    ) -> Self {
        SampleReceipt { oracle, first, count, rows, log_rows, full: true }
    }
    pub fn oracle(&self) -> u32 {
        self.oracle
    }
    pub fn first(&self) -> u32 {
        self.first
    }
    pub fn count(&self) -> u32 {
        self.count
    }
    pub fn rows(&self) -> u32 {
        self.rows
    }
    pub fn log_rows(&self) -> u32 {
        self.log_rows
    }
}

/// A receipt for tests and for the ported SEND block's eventual harness (mask.h:77-100). C++ tests
/// define their own `SendAccess` (`blocks/iop/tests/toy_support.h`); this is that door.
#[doc(hidden)]
pub fn receipt_for_a_test(oracle: u32, first: u32, count: u32, rows: u32, log_rows: u32) -> SampleReceipt {
    SampleReceipt::new(&SendAccess, oracle, first, count, rows, log_rows)
}

/// Gives out the free mask entries of one oracle message, each once, in increasing order
/// (`MaskLedger`, mask.h:113-145).
#[derive(Debug)]
pub struct MaskLedger {
    oracle: u32,
    next: u32,
    left: u32,
    rows: u32,
    log_rows: u32,
    closed: bool,
}

impl MaskLedger {
    /// `MaskLedger(SampleReceipt&&)` (mask.h:115-119). The receipt is consumed.
    pub fn new(receipt: SampleReceipt) -> Self {
        assert!(receipt.full, "MaskLedger: this receipt has been moved away or has made its ledger");
        MaskLedger {
            oracle: receipt.oracle,
            next: receipt.first,
            left: receipt.count,
            rows: receipt.rows,
            log_rows: receipt.log_rows,
            closed: false,
        }
    }

    /// One free entry, skipping numbers whose row is beyond the real rows (`take`, mask.h:125-131).
    pub fn take(&mut self) -> MaskSlot {
        assert!(!self.closed, "MaskLedger: a proximity test on this oracle message has begun");
        assert!(self.left > 0, "MaskLedger: the mask rows have no free entry left");
        while (self.next & ((1u32 << self.log_rows) - 1)) >= self.rows {
            self.next += 1;
        }
        self.left -= 1;
        let index = self.next;
        self.next += 1;
        MaskSlot::new(self.oracle, index)
    }

    pub fn take_n(&mut self, n: usize) -> Vec<MaskSlot> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(self.take());
        }
        v
    }

    pub fn left(&self) -> u32 {
        if self.closed {
            0
        } else {
            self.left
        }
    }

    pub fn close(&mut self) {
        self.closed = true;
    }
}
