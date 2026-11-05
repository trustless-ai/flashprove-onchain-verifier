//! The format's frame, ported from `blocks/frame/`.
//!
//! S2b-4 begins with the strict parameter parser; the derived sizes, plans and checks follow.

pub mod check;
pub mod check_entry;
pub mod check_key;
pub mod configure;
pub mod derive;
pub mod fields;
pub mod files;
pub mod heads;
pub mod hiding_conditions;
pub mod key_fixed;
pub mod lin_frame;
pub mod link_frame;
pub mod parameters;
pub mod prints;
pub mod req_frame;
pub mod wf_frame;
pub mod wf_units;
