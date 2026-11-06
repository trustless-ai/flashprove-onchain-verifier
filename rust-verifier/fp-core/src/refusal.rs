//! The verifier's two ways of ending early.
//!
//! C++ `refuse()` prints `NO: <name>` and calls `exit(1)` (`verifier/src/vf_common.h:53-59`);
//! a fault of the program prints `NOT CHECKED: <name>` and ends with status 5
//! (`verifier/src/cp_verify.cpp:2560-2566`). In the port they become values: the caller decides
//! how to print them. An `Internal` name is meant for a fault of the program, not of a proof.

use alloc::string::String;
use core::fmt;

/// A verifier rejection or an internal fault.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A check of the input failed: the call ends `NO: <name>`, status 1.
    Named(String),
    /// The program (or the machine) failed: the call ends `NOT CHECKED: <name>`, status 5.
    Internal(String),
}

impl Refusal {
    /// A rejection with the given C++ rejection name.
    pub fn named(name: &str) -> Self {
        Self::Named(String::from(name))
    }

    /// An internal fault with the given name (conventionally begins `internal-`).
    pub fn internal(name: &str) -> Self {
        Self::Internal(String::from(name))
    }

    /// The bare name, without a sub-proof prefix.
    pub fn name(&self) -> &str {
        match self {
            Self::Named(s) | Self::Internal(s) => s,
        }
    }

    /// True for a fault of the program or the machine.
    pub fn is_internal(&self) -> bool {
        matches!(self, Self::Internal(_))
    }
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The result type used throughout the verifier core.
pub type Result<T> = core::result::Result<T, Refusal>;
