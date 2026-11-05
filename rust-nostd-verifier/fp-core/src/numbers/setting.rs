//! `Setting` and the enums that classify rounds, ported from `blocks/numbers/setting.h`.

use alloc::string::String;

use super::real::Big;

/// What the verifier's message of a round consists of (`RoundKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RoundKind {
    Algebraic = 1,
    Epsilon = 2,
    Seed = 3,
    Positions = 4,
    Bits = 5,
    Seal = 6,
    Record = 7,
    Empty = 0,
}

/// The argument that bounds a round's error (`ErrorKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum ErrorKind {
    Field = 0,
    Sample = 1,
    Closeness = 2,
    Query = 3,
    Small = 4,
    Zero = 5,
}

/// Which bound gives the count of exceptional challenges (`CountSource`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CountSource {
    Third,
    Johnson,
}

/// How often a round's proof of work is paid (`Scope`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Scope {
    Request = 0,
    Shared = 1,
    Once = 2,
}

/// The inputs from which parameters, round errors and sizes are derived (`Setting`).
#[derive(Clone, Debug)]
pub struct Setting {
    pub field_name: String,
    pub p: Big,
    pub degree: u32,
    pub circle: bool,
    pub f_bytes: u32,
    pub e_bytes: u32,
    pub digest_bytes: u32,
    pub salt_bytes: u32,
    pub nonce_bytes: u32,
    pub position_bytes: u32,
    pub hash_block_bytes: u32,
    pub label_bytes: u32,
    pub chain_extra_bytes: u32,
    pub chain_free_words: u32,
    pub target: u32,
    pub instances: u64,
    pub samples: u32,
    pub saved_coefficient: bool,
    pub work: [[u32; 3]; 6],
}

impl Default for Setting {
    fn default() -> Self {
        Setting {
            field_name: String::new(),
            p: Big::zero(),
            degree: 3,
            circle: false,
            f_bytes: 8,
            e_bytes: 24,
            digest_bytes: 32,
            salt_bytes: 40,
            nonce_bytes: 8,
            position_bytes: 0,
            hash_block_bytes: 128,
            label_bytes: 16,
            chain_extra_bytes: 32,
            chain_free_words: 4,
            target: 128,
            instances: 1,
            samples: 1,
            saved_coefficient: true,
            work: [[0; 3]; 6],
        }
    }
}

impl Setting {
    pub fn card_e(&self) -> Big {
        Big::pow(self.p.clone(), self.degree as u64)
    }

    pub fn work_of(&self, k: ErrorKind, s: Scope) -> u32 {
        self.work[k as usize][s as usize]
    }

    pub fn set_work(&mut self, k: ErrorKind, s: Scope, bits: u32) {
        self.work[k as usize][s as usize] = bits;
    }

    /// `2^64 - 2^32 + 1`, cubic extension, plain Reed-Solomon codes (`setting_goldilocks`).
    pub fn goldilocks() -> Self {
        // p = 2^64 - 2^32 + 1.
        let p = Big::add(
            &Big::sub(&Big::two_to(64), &Big::two_to(32)),
            &Big::from_u64(1),
        );
        Setting { field_name: String::from("2^64 - 2^32 + 1"), p, circle: false, ..Setting::default() }
    }

    pub fn of_this_build() -> Self {
        Setting::goldilocks()
    }
}
