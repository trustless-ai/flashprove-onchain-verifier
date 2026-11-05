//! The base field F = Z/p and its cubic extension E, plus multilinear-polynomial helpers.
//!
//! Ported from `blocks/field/{gl64,field,mle}.h`.

pub mod ext;
pub mod gl64;
pub mod mle;

pub use ext::{F, E};
pub use gl64::{EPS, LOG2_P, NR, P};
