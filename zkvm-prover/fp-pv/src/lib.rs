//! The FlashProve public-values schema (`FPV1`) and the canonical input digest.
//!
//! This crate is compiled into the zkVM guest and into the host tools, so it is `#![no_std]` and
//! has no dependencies. The guest commits `pv::Values::encode()` first, then the human-readable
//! report, then the call's status; the contract decodes the first 128 bytes of the public values.
//! `inputs::input_digest` commits to the ten inputs the guest read, in a canonical order that the
//! host can recompute from the files.

#![no_std]

#[cfg(test)]
extern crate std;

pub mod inputs;
pub mod pv;
pub mod sha256;

pub use inputs::{input_digest, InputBundle, INPUT_DOMAIN};
pub use pv::{hex_decode_32, hex_encode_32, from_report, verdict, Values, MAGIC, PV_LEN, SCHEMA_VERSION};
pub use sha256::{sha256, Sha256};
