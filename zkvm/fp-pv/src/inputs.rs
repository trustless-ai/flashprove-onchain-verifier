//! The canonical input bundle and its digest.
//!
//! The guest reads ten values: policy.txt, layout.txt, KL.bin, key.bin, the leaf file, the leaf
//! number, request, y, proof, and the commitment ID. The digest below is computed over those ten
//! values in that order, with a domain separator and a length prefix on every variable-length
//! field, so that moving bytes between two fields changes the digest. It does not depend on SP1's
//! stdin serialization: a provider computes it from the files, the guest computes it from the
//! values it read, and both must agree.

use crate::sha256::Sha256;

/// Bumped only when the layout below changes; the guest and every host tool compare this string in
/// their documentation. A change to it is a new public-values schema.
pub const INPUT_DOMAIN: &[u8] = b"FlashProve/input-v1\0";

/// The ten inputs in the guest's read order.
pub struct InputBundle<'a> {
    pub policy: &'a [u8],
    pub layout: &'a [u8],
    pub kl: &'a [u8],
    pub key: &'a [u8],
    pub entry: &'a [u8],
    pub entry_number: u32,
    pub request: &'a [u8],
    pub y: &'a [u8],
    pub proof: &'a [u8],
    pub id: &'a str,
}

fn feed(h: &mut Sha256, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// SHA-256 of `INPUT_DOMAIN || len(policy) || policy || ... || len(id) || id`.
///
/// `entry_number` is four bytes, little-endian, with no length prefix (it is fixed size).
#[must_use]
pub fn input_digest(bundle: &InputBundle<'_>) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(INPUT_DOMAIN);
    feed(&mut h, bundle.policy);
    feed(&mut h, bundle.layout);
    feed(&mut h, bundle.kl);
    feed(&mut h, bundle.key);
    feed(&mut h, bundle.entry);
    h.update(&bundle.entry_number.to_le_bytes());
    feed(&mut h, bundle.request);
    feed(&mut h, bundle.y);
    feed(&mut h, bundle.proof);
    feed(&mut h, bundle.id.as_bytes());
    h.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bundle<'a>(
        policy: &'a [u8],
        layout: &'a [u8],
        proof: &'a [u8],
        id: &'a str,
    ) -> InputBundle<'a> {
        InputBundle {
            policy,
            layout,
            kl: b"KL",
            key: b"KEY",
            entry: b"ENTRY",
            entry_number: 7,
            request: b"REQ",
            y: b"Y",
            proof,
            id,
        }
    }

    #[test]
    fn deterministic() {
        let a = bundle(b"pol", b"lay", b"proof", "00");
        let b = bundle(b"pol", b"lay", b"proof", "00");
        assert_eq!(input_digest(&a), input_digest(&b));
    }

    #[test]
    fn every_field_counts() {
        let base = bundle(b"pol", b"lay", b"proof", "00");
        let want = input_digest(&base);
        assert_ne!(input_digest(&bundle(b"poL", b"lay", b"proof", "00")), want);
        assert_ne!(input_digest(&bundle(b"pol", b"laY", b"proof", "00")), want);
        assert_ne!(input_digest(&bundle(b"pol", b"lay", b"prooF", "00")), want);
        assert_ne!(input_digest(&bundle(b"pol", b"lay", b"proof", "01")), want);
    }

    #[test]
    fn field_boundaries_are_covered() {
        // Moving one byte from policy to layout must change the digest, because each field is
        // length-prefixed.
        let a = bundle(b"ab", b"c", b"proof", "00");
        let b = bundle(b"a", b"bc", b"proof", "00");
        assert_ne!(input_digest(&a), input_digest(&b));
    }

    #[test]
    fn entry_number_is_little_endian() {
        let mut a = bundle(b"p", b"l", b"q", "00");
        a.entry_number = 1;
        let mut b = bundle(b"p", b"l", b"q", "00");
        b.entry_number = 256;
        assert_ne!(input_digest(&a), input_digest(&b));
    }
}
