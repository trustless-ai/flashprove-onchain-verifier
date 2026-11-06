//! Headers of the key, leaf and proof files, the configuration digest, the commitment ID and the
//! labels of four hash chains (`blocks/frame/heads.h`).
//!
//! A header is two or three little-endian 32-bit words: its tag, the version word and, in a proof
//! file only, the number of the leaf table. A chain's label and the configuration digest enter its
//! first query.

use crate::chain::rounds::SampleSeed;
use crate::consts::{TAG_ENTRY, TAG_KEY, TAG_PROOF, PROGRAM_VERSION_WORD};
use crate::field::ext::E;
use crate::hash::calls::HashCalls;
use crate::hash::domains::Domain;
use crate::hash::modes::{Digest, Hasher, Tag};
use crate::iop::message::Reader;

/// `TAG_KEY`, `TAG_ENTRY` and `TAG_PROOF` (`heads.h:31`).
pub const HEAD_TAG_KEY: u32 = TAG_KEY;
pub const HEAD_TAG_ENTRY: u32 = TAG_ENTRY;
pub const HEAD_TAG_PROOF: u32 = TAG_PROOF;

/// `read_head()` (`heads.h:47-52`): the tag and this build's version word, or why not. On a
/// failure every later read from `r` fails too.
pub fn read_head(r: &mut Reader<'_>, tag: u32) -> Option<&'static str> {
    let mut t = 0u32;
    let mut v = 0u32;
    let why = if !get_word(r, &mut t) || !get_word(r, &mut v) {
        Some("file-too-short")
    } else if t != tag {
        Some("file-of-another-kind")
    } else if v != PROGRAM_VERSION_WORD {
        Some("version-unknown")
    } else {
        None
    };
    if why.is_some() {
        r.refuse();
    }
    why
}

/// `read_head(.., entry)` (`heads.h:54-58`): also the leaf table's number, which the caller checks.
pub fn read_head_entry(r: &mut Reader<'_>, tag: u32) -> Result<u32, &'static str> {
    if let Some(why) = read_head(r, tag) {
        return Err(why);
    }
    let mut entry = 0u32;
    if !get_word(r, &mut entry) {
        return Err("file-too-short");
    }
    Ok(entry)
}

/// `get_word()` (`heads.h:37-42`).
fn get_word(r: &mut Reader<'_>, x: &mut u32) -> bool {
    let Some(b) = r.take(4) else { return false };
    *x = (b[0] as u32) | ((b[1] as u32) << 8) | ((b[2] as u32) << 16) | ((b[3] as u32) << 24);
    true
}

/// `parameter_file_digest()` (`heads.h:61-65`): the parameter file's text alone.
pub fn parameter_file_digest(text: &[u8], calls: &mut HashCalls) -> Digest {
    let mut h = Hasher::new(&Tag::plain(Domain::Parameters, 0), 0, calls);
    h.push(text);
    h.finish()
}

/// `configuration_digest()` (`heads.h:71-76`): every byte of the public files, each file's length
/// before its bytes, in the caller's order (the parameter file first).
pub fn configuration_digest(files: &[&[u8]], calls: &mut HashCalls) -> Digest {
    let mut h = Hasher::new(&Tag::plain(Domain::Parameters, 0), 2, calls);
    h.push_u64(files.len() as u64);
    for f in files {
        h.push_u64(f.len() as u64);
        h.push(f);
    }
    h.finish()
}

/// `published_id()` (`heads.h:91-106`): the commitment ID, by which a client names a commitment.
pub fn published_id(
    configuration: &Digest,
    first_table_name: &[u8],
    record_seeds: &[SampleSeed],
    record_answers: &[E],
    calls: &mut HashCalls,
) -> Digest {
    let mut h = Hasher::new(&Tag::plain(Domain::PublishedId, 0), 0, calls);
    h.push_digest(configuration);
    h.push_u64(first_table_name.len() as u64);
    h.push(first_table_name);
    let elements: u64 = record_seeds.iter().map(|s| s.z.len() as u64 + 1).sum();
    h.push_u64(elements);
    for s in record_seeds {
        for x in &s.z {
            h.push_e(*x);
        }
        h.push_e(s.beta);
    }
    h.push_u64(record_answers.len() as u64);
    for y in record_answers {
        h.push_e(*y);
    }
    h.push_u64(0);
    h.finish()
}

/// The labels of a proof file's three chains and a key file's first (`heads.h:112`).
pub const LABEL_FIRST_CHAIN: u64 = 0x46524d01;
pub const LABEL_ONE_TIME_CHAIN: u64 = 0x46524d02;
pub const LABEL_PROOF_SHARED_CHAIN: u64 = 0x46524d03;
pub const LABEL_PROOF_SECOND_CHAIN: u64 = 0x46524d04;

/// The labels listed in rising order, as `configure.h:33-36` asserts.
pub fn labels_are_ordered() -> bool {
    LABEL_FIRST_CHAIN < LABEL_ONE_TIME_CHAIN
        && LABEL_ONE_TIME_CHAIN < LABEL_PROOF_SHARED_CHAIN
        && LABEL_PROOF_SHARED_CHAIN < LABEL_PROOF_SECOND_CHAIN
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::iop::message::Reader;

    #[test]
    fn header_words_are_little_endian_and_checked() {
        let mut r = Reader::new(&[b'C', b'P', b'I', b'K', 0x48, 0x38, 0x32, 0x31]);
        assert_eq!(read_head(&mut r, TAG_KEY), None);
        assert!(r.at_end());

        let mut r = Reader::new(&[b'C', b'P', b'P', b'F', 0x48, 0x37, 0x32, 0x31]);
        assert_eq!(read_head(&mut r, TAG_PROOF), Some("version-unknown"));

        let mut r = Reader::new(&[b'C', b'P', b'E', b'N', 0x48]);
        assert_eq!(read_head_entry(&mut r, TAG_ENTRY), Err("file-too-short"));
    }

    #[test]
    fn labels_are_in_rising_order() {
        assert!(labels_are_ordered());
    }
}
