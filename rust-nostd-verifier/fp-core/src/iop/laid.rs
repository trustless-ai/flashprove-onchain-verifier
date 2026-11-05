//! Matrix layouts and their coefficient forms, ported from `blocks/iop/laid.h` (lines 37-195).
//! The prover's engine-held weight vector (`IndexWeights::held`) is not reachable from a verifier;
//! the port keeps only the product form and the written-out vector.

use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;

use super::tensor::{Form, Tensor};
use crate::chain::public::PublicBytes;
use crate::field::ext::E;
use crate::iop::message::Writer;

/// An aligned block of a matrix in a table (`LaidBlock`, laid.h:37-41).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LaidBlock {
    pub first_i: u64,
    pub first_c: u64,
    pub first_row: u64,
    pub first_place: u64,
    pub bits_i: u32,
    pub bits_c: u32,
    pub row_bits: u32,
    pub place_bits: u32,
    pub i_is_low: bool,
}

impl PublicBytes for LaidBlock {
    /// `public_bytes(Writer&, const LaidBlock&)` (laid.h:44-46).
    fn public_bytes(&self, w: &mut Writer) {
        for x in [
            self.first_i,
            self.first_c,
            self.first_row,
            self.first_place,
            self.bits_i as u64,
            self.bits_c as u64,
            self.row_bits as u64,
            self.place_bits as u64,
            self.i_is_low as u64,
        ] {
            w.put_u64(x);
        }
    }
    /// `public_fault(const LaidBlock&)` (laid.h:50-55).
    fn public_fault(&self) -> Option<&'static str> {
        if laid_block_ok_geometry(self) {
            None
        } else {
            Some("laid: a block that is not aligned, or of another size in the table than in its matrix")
        }
    }
}

fn aligned(first: u64, bits: u32) -> bool {
    bits < 48 && first >> 48 == 0 && (first >> bits << bits) == first
}

/// `laid_block_ok` (laid.h:56-61).
pub fn laid_block_ok(b: &LaidBlock, table_row_bits: u32, table_place_bits: u32) -> bool {
    laid_block_ok_geometry(b)
        && b.row_bits <= table_row_bits
        && b.place_bits <= table_place_bits
        && (b.first_row >> table_row_bits) == 0
        && (b.first_place >> table_place_bits) == 0
}

fn laid_block_ok_geometry(b: &LaidBlock) -> bool {
    b.row_bits + b.place_bits == b.bits_i + b.bits_c
        && aligned(b.first_i, b.bits_i)
        && aligned(b.first_c, b.bits_c)
        && aligned(b.first_row, b.row_bits)
        && aligned(b.first_place, b.place_bits)
}

/// One matrix of a layout (`LaidMatrix`, laid.h:64-67).
#[derive(Clone, Debug, Default)]
pub struct LaidMatrix {
    pub size_i: u64,
    pub size_c: u64,
    pub blocks: Vec<LaidBlock>,
}

fn meet(a: u64, a_bits: u32, b: u64, b_bits: u32) -> bool {
    a < b + (1u64 << b_bits) && b < a + (1u64 << a_bits)
}

/// `laid_ok` (laid.h:72-95).
pub fn laid_ok(matrices: &[LaidMatrix], table_row_bits: u32, table_place_bits: u32) -> bool {
    let mut all: Vec<&LaidBlock> = Vec::new();
    for m in matrices {
        let mut covered: u128 = 0;
        for (x, b) in m.blocks.iter().enumerate() {
            if !laid_block_ok(b, table_row_bits, table_place_bits) {
                return false;
            }
            if b.first_i + (1u64 << b.bits_i) > m.size_i
                || b.first_c + (1u64 << b.bits_c) > m.size_c
            {
                return false;
            }
            for y in &m.blocks[..x] {
                if meet(b.first_i, b.bits_i, y.first_i, y.bits_i)
                    && meet(b.first_c, b.bits_c, y.first_c, y.bits_c)
                {
                    return false;
                }
            }
            covered += 1u128 << (b.bits_i + b.bits_c);
            all.push(b);
        }
        if covered != m.size_i as u128 * m.size_c as u128 {
            return false;
        }
    }
    for x in 0..all.len() {
        for y in 0..x {
            if meet(all[x].first_row, all[x].row_bits, all[y].first_row, all[y].row_bits)
                && meet(all[x].first_place, all[x].place_bits, all[y].first_place, all[y].place_bits)
            {
                return false;
            }
        }
    }
    true
}

/// Weights on one index of a matrix (`IndexWeights`, laid.h:100-131). The product form has `lo` and
/// `hi` of equal length; a written-out vector has `values`.
#[derive(Clone, Debug, Default)]
pub struct IndexWeights {
    pub lo: Vec<E>,
    pub hi: Vec<E>,
    pub values: Option<Rc<Vec<E>>>,
}

impl IndexWeights {
    pub fn written_out(&self) -> bool {
        self.values.is_some()
    }
    pub fn eq(point: &[E]) -> Self {
        let mut w = IndexWeights::default();
        for z in point {
            w.lo.push(E::one() - *z);
            w.hi.push(*z);
        }
        w
    }
    pub fn powers(mut base: E, bits: u32) -> Self {
        let mut w = IndexWeights::default();
        for _ in 0..bits {
            w.lo.push(E::one());
            w.hi.push(base);
            base = base * base;
        }
        w
    }
    pub fn written(values: Rc<Vec<E>>) -> Self {
        IndexWeights { lo: Vec::new(), hi: Vec::new(), values: Some(values) }
    }
}

/// `scalar * on_i[i] * on_c[c]` on the block's table entries (`laid_tensor`, laid.h:137-187).
pub fn laid_tensor(
    b: &LaidBlock,
    table_row_bits: u32,
    table_place_bits: u32,
    on_i: &IndexWeights,
    on_c: &IndexWeights,
    scalar: E,
) -> Tensor {
    assert!(
        laid_block_ok(b, table_row_bits, table_place_bits),
        "laid: a block that is not aligned or does not fit the table"
    );
    assert!(
        !(on_i.written_out() && on_c.written_out()),
        "laid: only one of the two weights can be a written-out vector"
    );
    let mut t = Tensor::default();
    t.scalar = scalar;
    let mut dense: Vec<(u32, u32)> = Vec::new();
    let low_bits = if b.i_is_low { b.bits_i } else { b.bits_c };
    let mut push_bit_of_x = |t: &mut Tensor, x_bit: u32| {
        let of_i = (x_bit < low_bits) == b.i_is_low;
        let bit = if x_bit < low_bits { x_bit } else { x_bit - low_bits };
        let w = if of_i { on_i } else { on_c };
        if w.written_out() {
            dense.push((bit, t.vars()));
            t.push(E::one(), E::one());
        } else {
            assert!(
                (bit as usize) < w.lo.len(),
                "laid: a product form with too few bits for its index"
            );
            t.push(w.lo[bit as usize], w.hi[bit as usize]);
        }
    };
    for x in b.place_bits..b.place_bits + b.row_bits {
        push_bit_of_x(&mut t, x);
    }
    t.insert_choice(t.vars(), table_row_bits - b.row_bits, b.first_row >> b.row_bits);
    for x in 0..b.place_bits {
        push_bit_of_x(&mut t, x);
    }
    t.insert_choice(t.vars(), table_place_bits - b.place_bits, b.first_place >> b.place_bits);
    let above = |t: &mut Tensor, w: &IndexWeights, first: u64, bits: u32| {
        if w.written_out() {
            return;
        }
        assert!(
            w.lo.len() >= 64 || (first >> w.lo.len()) == 0,
            "laid: a product form with too few bits for its index"
        );
        for i in bits..w.lo.len() as u32 {
            t.scalar = t.scalar * (if (first >> i) & 1 != 0 { w.hi[i as usize] } else { w.lo[i as usize] });
        }
    };
    above(&mut t, on_i, b.first_i, b.bits_i);
    above(&mut t, on_c, b.first_c, b.bits_c);
    if let Some(values) = on_i.values.as_ref().or(on_c.values.as_ref()) {
        let first = if on_i.values.is_some() { b.first_i } else { b.first_c };
        if dense.is_empty() {
            assert!(first < values.len() as u64, "laid: the written-out vector is too short");
            t.scalar = t.scalar * values[first as usize];
        } else {
            t.dense_vars = vec![0u32; dense.len()];
            for (bit, var) in &dense {
                t.dense_vars[*bit as usize] = *var;
            }
            t.set_values(values.clone(), first);
        }
    }
    t
}

/// The sum of `laid_tensor` over one matrix's blocks (`laid_form`, laid.h:190-195).
pub fn laid_form(
    blocks: &[LaidBlock],
    table_row_bits: u32,
    table_place_bits: u32,
    on_i: &IndexWeights,
    on_c: &IndexWeights,
    scalar: E,
) -> Form {
    let mut f = Form::default();
    for b in blocks {
        f.add(laid_tensor(b, table_row_bits, table_place_bits, on_i, on_c, scalar));
    }
    f
}
