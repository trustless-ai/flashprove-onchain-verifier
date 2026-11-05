//! Reed-Solomon codes, cosets and short positions (`blocks/code/`).

pub mod code;
pub mod cosets;
pub mod short_position;

pub use code::{code_ok, Code, Encoder};
pub use short_position::short_position;
