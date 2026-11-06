//! FlashProve verifier core, ported from `verifier/src`.
//!
//! Scope: constants, the refusal model, header checks, rejection names, the output-parsing
//! helpers and the per-stage state container. The proof system arrives with the rest of the port.
//!
//! This crate is `#![no_std]` and allocates only through `alloc`.

#![no_std]

extern crate alloc;

pub mod chain;
pub mod code;
pub mod consts;
pub mod field;
pub mod frame;
pub mod hash;
pub mod head;
pub mod iop;
pub mod names;
pub mod numbers;
pub mod out;
pub mod refusal;
pub mod stage_state;
pub mod tree;
pub mod verifier;
