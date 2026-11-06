//! The round names of a hash chain, ported from `blocks/numbers/round_names.h` (lines 20-50).
//! The strings are part of the proof format: they are hashed into the chain's first query.

pub const R_SEND_SEED: &str = "SEND seed";
pub const R_SEND_ANSWER: &str = "SEND answer";
pub const R_BAT: &str = "BAT";
pub const R_BAT_SIGMA: &str = "BAT-sigma";
pub const R_SPLIT: &str = "SPLIT";
pub const R_PSC_EPSILON: &str = "PSC epsilon";
pub const R_PSC_ROUND: &str = "PSC round";
pub const R_PSC_Y: &str = "PSC Y";
pub const R_PSC_VALUES: &str = "PSC values";
pub const R_ZERO: &str = "ZERO";
pub const R_LINE: &str = "LINE";
pub const R_LKP_SHIFT: &str = "LKP shift";
pub const R_JOIN: &str = "JOIN";
pub const R_LKP_PLANES: &str = R_JOIN;
pub const R_FOREST_POINT: &str = R_JOIN;
pub const R_LKP: &str = "LKP";
pub const R_RNG: &str = "RNG";
pub const R_FOLD_EPSILON: &str = "FOLD epsilon";
pub const R_FOLD_ROUND: &str = "FOLD round";
pub const R_LOC: &str = "LOC";
pub const R_CS: &str = "CS";
pub const R_BASE_LAMBDA: &str = "BASE lambda";
pub const R_BASE: &str = "BASE";
pub const R_SEAL: &str = "SEAL";
pub const R_LAST: &str = "LAST";
pub const R_REPLY: &str = "REPLY";
pub const R_RECORD: &str = "RECORD";
pub const R_LIN_POINT: &str = "LIN point";
pub const R_LIN_ZETA: &str = "LIN zeta";
pub const R_LINK_POINT: &str = "LINK point";
pub const R_LINK: &str = "LINK";
pub const R_LINK_PHI: &str = "LINK phi";
