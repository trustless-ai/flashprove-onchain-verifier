//! The public inputs to the first queries of a key file's three hash chains, ported from
//! `blocks/frame/key_fixed.h`.
//!
//! The one-time chain's first query contains all six members of `KeyFixed`, the shared chain's
//! contains `configuration`, `codes` and `lin`, and the second chain's contains `configuration`
//! alone, each as `public_bytes()` writes it. The members follow from the public files, some of
//! them through the calling program's `ShapesOf` function, so `configure` rejects unusable files,
//! with `key_fault()`'s reason, before a table is committed.

use alloc::vec::Vec;

use crate::chain::public::PublicBytes;
use crate::frame::files::Sized;
use crate::hash::modes::Digest;
use crate::iop::context::OracleNotice;
use crate::iop::lin::{lin_fault, LinBindingShape, LinShape};
use crate::iop::message::Writer;
use crate::iop::relation::Codes;
use crate::iop::send_pad::free_mask_entries;
use crate::iop::wf::{wf_fault, wf_index_mask_entries, wf_matrix_of, WfPublic};

/// What a key file fixes before its first chain (`KeyFixed`, key_fixed.h:27-34). `ranges`: WF, the
/// range proof on the table's entries. `index_masks`: the index-mask message's shape; WF and BATT
/// (which joins WF's claims) use its mask entries.
#[derive(Clone, Debug, Default)]
pub struct KeyFixed {
    pub configuration: Digest,
    pub codes: Codes,
    /// The committer's one-time test: a batch of one, at its own distance.
    pub lin: LinShape,
    pub index_masks: OracleNotice,
    pub ranges: WfPublic,
    /// One leaf.
    pub binding: LinBindingShape,
}

/// `key_fixed` (key_fixed.h:35-41). `make_key()` and `check_key()` build this only from their
/// `Configured` argument; here the caller passes the configuration digest.
pub fn key_fixed(z: &Sized, configuration: &Digest) -> KeyFixed {
    KeyFixed {
        configuration: *configuration,
        codes: z.key_codes.clone(),
        lin: z.once.s.clone(),
        index_masks: z.once.input.clone(),
        ranges: z.ranges.x.clone(),
        binding: LinBindingShape { log_leaves: 0, salt_bytes: z.d.set.salt_bytes as usize },
    }
}

/// `key_public_bytes` (key_fixed.h:59-65): every member of `f`, but neither the text labels
/// (`OracleShape::name`, `WfLookup::name`) nor the table's test distances (`IndexShape::distances`,
/// in `f.lin`).
pub fn key_public_bytes(f: &KeyFixed) -> Vec<u8> {
    let mut w = Writer::default();
    w.put_digest(&f.configuration);
    f.codes.public_bytes(&mut w);
    f.lin.public_bytes(&mut w);
    f.index_masks.public_bytes(&mut w);
    f.ranges.public_bytes(&mut w);
    f.binding.public_bytes(&mut w);
    w.bytes().to_vec()
}

/// `key_fault` (key_fixed.h:69-80): `None`, or why no key file can be made or checked under `f`,
/// including conditions across several fields.
pub fn key_fault(f: &KeyFixed) -> Option<&'static str> {
    if let Some(w) = lin_fault(&f.codes, &f.lin) {
        return Some(w);
    }
    // `WfPublic` does not store the matrix's size.
    let matrix = wf_matrix_of(&f.lin);
    if let Some(w) = wf_fault(&f.codes, &f.ranges, &matrix) {
        return Some(w);
    }
    if f.binding.log_leaves != 0 {
        return Some("a key's binding tree has one leaf");
    }
    if f.ranges.message_id != 1 {
        return Some("the multiplicities' message is the second oracle message of the one-time chain");
    }
    let m = &f.index_masks.shape;
    if m.main_rows != 0
        || m.mask_rows == 0
        || m.answers < 1
        || m.mask_code as usize >= f.codes.mask.len()
    {
        return Some("the index-mask message is a sampled message of mask rows alone");
    }
    let room = free_mask_entries(
        m.mask_rows,
        f.codes.mask[m.mask_code as usize].ell,
        m.answers,
    );
    if wf_index_mask_entries(&f.ranges, &matrix) as u64 > room {
        return Some("the index-mask message has no room for the entries that the ranges and the joining take");
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::iop::wf::WfMatrix;

    fn empty() -> KeyFixed {
        KeyFixed::default()
    }

    #[test]
    fn an_empty_key_faults_on_its_lin_shape_first() {
        // `key_fault` reports `lin_fault` before the fields that follow it.
        let f = empty();
        assert!(key_fault(&f).is_some());
        assert_eq!(key_fault(&f), lin_fault(&f.codes, &f.lin));
    }

    #[test]
    fn key_fixed_copies_the_sized_ones() {
        // No `Sized` is needed for the empty one: every member is a copy of a default.
        let z = crate::frame::files::Sized::default();
        let d = Digest { w: [7; 8] };
        let f = key_fixed(&z, &d);
        assert_eq!(f.configuration, d);
        assert!(f.codes.base.is_empty() && f.codes.mask.is_empty());
        assert_eq!(f.binding, LinBindingShape { log_leaves: 0, salt_bytes: 40 });
        assert!(f.ranges.lookups.is_empty());
        assert_eq!(f.index_masks.shape.answers, 1);
    }

    #[test]
    fn public_bytes_has_one_length_for_one_key() {
        let f = empty();
        let b = key_public_bytes(&f);
        // configuration (32) + codes (two lengths) + the default shapes.
        assert!(b.len() >= 32 + 16);
        let g = KeyFixed {
            configuration: Digest { w: [1, 2, 3, 4, 5, 6, 7, 8] },
            ..f
        };
        let c = key_public_bytes(&g);
        assert_eq!(c.len(), b.len());
        assert_ne!(c[..32], b[..32]);
    }

    #[test]
    fn the_matrix_comes_from_the_lin_shape() {
        let m = WfMatrix { k_col: 3, rows: 9 };
        assert_eq!(wf_matrix_of(&LinShape { k_lo: 1, matrix_rows: 9, ..LinShape::default() }), WfMatrix { k_col: 1, rows: 9 });
        assert_eq!(m.k_row(), 4);
    }
}
