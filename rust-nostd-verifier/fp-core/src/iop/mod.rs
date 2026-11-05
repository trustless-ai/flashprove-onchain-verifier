//! The protocol blocks over the hash chain (`blocks/iop/`).
//!
//! Parameter names such as `S`, `V`, `T`, `G` and `L` keep their C++ spellings so that a reader
//! can follow the source beside this port; `non_snake_case` is allowed for that reason.

#![allow(non_snake_case)]


pub mod base_case;
pub mod bat;
pub mod batt;
pub mod batt_shown;
pub mod context;
pub mod cs;
pub mod fold;
pub mod fold_algebra;
pub mod fold_rounds;
pub mod foldeq;
pub mod hp;
pub mod iopp;
pub mod laid;
pub mod lin;
pub mod line;
pub mod link;
pub mod lkp;
pub mod mask;
pub mod member;
pub mod message;
pub mod psc;
pub mod psc_rows;
pub mod relation;
pub mod req;
pub mod req_rows;
pub mod rng;
pub mod send;
pub mod send_pad;
pub mod single_rows;
pub mod split;
pub mod summand;
pub mod tensor;
pub mod wf;
