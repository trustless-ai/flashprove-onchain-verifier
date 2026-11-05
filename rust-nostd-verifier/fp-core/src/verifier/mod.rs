//! The verifier's shared core, its transcript adapter, its public tables and digest gate, and the
//! sub-proof engine with its smallness test, lookup argument and sumchecks.

pub mod attention_check;
pub mod attention_plan;
pub mod attention_run;
pub mod attention_shape;
pub mod common;
pub mod engine;
pub mod frame_segment;
pub mod head_check;
pub mod head_plan;
pub mod head_rounds;
pub mod layers_check;
pub mod layers_plan;
pub mod layers_rounds;
pub mod lookup;
pub mod matrices;
pub mod norm_digit_rows;
pub mod packing;
pub mod request_chain;
pub mod run_stage;
pub mod segments;
pub mod segment;
pub mod smallness;
pub mod stage_context;
pub mod stage_layout;
pub mod stage_links;
pub mod sumcheck;
pub mod tables;
pub mod transcript;
pub mod weights_layout;
pub mod weights_merge;
pub mod weights_pending;
