//! `Tweak`, ported from `blocks/hash/tweak.h:44-51`.
//!
//! F's flag and F's 128-bit counter as the four words c0, c1, num and l, lowest first. The struct
//! declares `l` before `num`, as C++ does.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tweak {
    pub c0: u32,
    pub c1: u32,
    pub l: u32,
    pub num: u32,
    pub last: bool,
}
