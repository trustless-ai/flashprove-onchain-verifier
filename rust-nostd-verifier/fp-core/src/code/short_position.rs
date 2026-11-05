//! The short position `x mod 2^log_short`, ported from `blocks/code/short_position.h`.

/// The position at which a shorter codeword is read when a longer one is read at `x`.
#[inline]
pub fn short_position(_log_n: u32, log_short: u32, x: u64) -> u64 {
    x & ((1u64 << log_short) - 1)
}
