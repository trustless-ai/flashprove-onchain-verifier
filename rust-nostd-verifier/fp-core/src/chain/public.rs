//! Public inputs and the first query, ported from `blocks/chain/public.h`.
//!
//! A `Public<T>` is a value that stands in a first query: only a `Binder`, `derive()` and
//! `element()` make one that is not empty, and `VerifierRounds::get()` returns the value after
//! checking that it stands in this chain or in a chain that it follows. The marks are `Rc`s; their
//! identity, not their contents, says which Binder bound a value.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use super::chain::FirstQuery;
use crate::consts::{BLK_FIELD, BLK_HASH, PROGRAM_VERSION_WORD};
use crate::field::ext::{F, E};
use crate::hash::calls::HashCalls;
use crate::hash::domains::Domain;
use crate::hash::modes::{Digest, Hasher, Tag};
use crate::iop::message::Writer;
use crate::numbers::plan::Planned;

/// Identifies the Binder, and so the first query, that bound a value (`PublicMark`).
pub type PublicMark = Rc<u8>;

/// Canonical bytes of a public value (`public_bytes`), and its self-contradictions (`public_fault`).
pub trait PublicBytes {
    fn public_bytes(&self, w: &mut Writer);
    fn public_fault(&self) -> Option<&'static str> {
        None
    }
}

macro_rules! public_integer {
    ($($t:ty),*) => {$(
        impl PublicBytes for $t {
            fn public_bytes(&self, w: &mut Writer) {
                w.put_u64(*self as u64);
            }
        }
    )*};
}
public_integer!(u8, u16, u32, u64, usize, i8, i16, i32, i64);

impl PublicBytes for bool {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(*self as u64);
    }
}
impl PublicBytes for F {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_f(*self);
    }
}
impl PublicBytes for E {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_e(*self);
    }
}
impl PublicBytes for Digest {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_digest(self);
    }
}
impl PublicBytes for String {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.len() as u64);
        w.put_bytes(self.as_bytes());
    }
}
/// A byte string: its length as one 64-bit word, then the raw bytes.
impl PublicBytes for Vec<u8> {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.len() as u64);
        w.put_bytes(self);
    }
}
/// A list of 64-bit words: its length, then each word (`public_bytes`'s vector form,
/// `blocks/chain/public.h:64-67`; the byte vector above is the non-template overload).
impl PublicBytes for Vec<u64> {
    fn public_bytes(&self, w: &mut Writer) {
        w.put_u64(self.len() as u64);
        for x in self {
            w.put_u64(*x);
        }
    }
}
impl<A: PublicBytes, B: PublicBytes> PublicBytes for (A, B) {
    fn public_bytes(&self, w: &mut Writer) {
        self.0.public_bytes(w);
        self.1.public_bytes(w);
    }
}

/// A bound value (`Public<T>`). The default stands in no query.
pub struct Public<T> {
    mark: Option<PublicMark>,
    value: Option<Rc<T>>,
}

impl<T> Default for Public<T> {
    fn default() -> Self {
        Public { mark: None, value: None }
    }
}

impl<T> Clone for Public<T> {
    fn clone(&self) -> Self {
        Public { mark: self.mark.clone(), value: self.value.clone() }
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for Public<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Public").field("value", &self.value).finish()
    }
}

impl<T> Public<T> {
    /// `f(x)`, for a value computed from bound values only (`derive`).
    pub fn derive<U>(&self, f: impl FnOnce(&T) -> U) -> Public<U> {
        assert!(self.value.is_some(), "public input: a value that stands in no first query");
        Public { mark: self.mark.clone(), value: Some(Rc::new(f(self.value.as_ref().unwrap()))) }
    }

    pub(crate) fn is_bound(&self) -> bool {
        self.value.is_some()
    }
    pub(crate) fn mark(&self) -> Option<&PublicMark> {
        self.mark.as_ref()
    }
    pub(crate) fn value(&self) -> Option<&T> {
        self.value.as_deref()
    }
    pub(crate) fn new(mark: PublicMark, value: T) -> Self {
        Public { mark: Some(mark), value: Some(Rc::new(value)) }
    }
}

/// `f(a, b)`, for two values bound by one Binder (`derive`).
pub fn derive<A, B, R>(
    a: &Public<A>,
    b: &Public<B>,
    f: impl FnOnce(&A, &B) -> R,
) -> Public<R> {
    assert!(
        a.is_bound() && b.is_bound() && a.mark().is_some() && b.mark().is_some() && Rc::ptr_eq(a.mark().unwrap(), b.mark().unwrap()),
        "public input: two values of two first queries"
    );
    Public {
        mark: a.mark.clone(),
        value: Some(Rc::new(f(a.value.as_ref().unwrap(), b.value.as_ref().unwrap()))),
    }
}

/// Entry `i` of a bound vector (`element`).
pub fn element<U: Clone>(v: &Public<Vec<U>>, i: usize) -> Public<U> {
    assert!(
        v.is_bound() && i < v.value.as_ref().unwrap().len(),
        "public input: no such entry"
    );
    Public { mark: v.mark.clone(), value: Some(Rc::new(v.value.as_ref().unwrap()[i].clone())) }
}

/// The state of one chain, shared with every chain that follows it (`ChainFate`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ChainFate {
    pub refused: bool,
    pub ended: bool,
}

pub(crate) type SharedFate = Rc<core::cell::Cell<ChainFate>>;

/// The end of a chain (`Sealed`).
#[derive(Clone, Default)]
pub struct Sealed {
    pub(crate) marks: Vec<PublicMark>,
    pub(crate) digest: Digest,
    pub(crate) instance: Digest,
    pub(crate) fates: Vec<SharedFate>,
}

impl Sealed {
    pub fn digest(&self) -> &Digest {
        assert!(!self.marks.is_empty(), "public input: the seal of no chain");
        &self.digest
    }
    pub(crate) fn new(
        marks: Vec<PublicMark>,
        digest: Digest,
        fates: Vec<SharedFate>,
        instance: Digest,
    ) -> Self {
        Sealed { marks, digest, instance, fates }
    }
}

/// Builds a chain's first query (`Binder`).
pub struct Binder {
    pub(crate) label: u64,
    pub(crate) plan: Rc<Planned>,
    pub(crate) mark: PublicMark,
    pub(crate) earlier: Vec<PublicMark>,
    pub(crate) earlier_instances: Vec<Digest>,
    pub(crate) parameters: Writer,
    pub(crate) statement: Writer,
    pub(crate) salted: bool,
    pub(crate) salt_in_proof: bool,
    pub(crate) has_configuration: bool,
    pub(crate) other_items: bool,
    pub(crate) salt: Digest,
    pub(crate) configuration: Digest,
    pub(crate) earlier_fates: Vec<SharedFate>,
    pub(crate) parameters_closed: bool,
    pub(crate) closed: bool,
}

impl Binder {
    /// The parameters begin with the version word and the plan (`Binder`).
    pub fn new(label: u64, plan: Rc<Planned>) -> Self {
        let mut parameters = Writer::default();
        let version_name = "the format's version";
        parameters.put_u64(version_name.len() as u64);
        parameters.put_bytes(version_name.as_bytes());
        parameters.put_u64(8);
        parameters.put_u64(PROGRAM_VERSION_WORD as u64);
        for x in [
            BLK_FIELD,
            BLK_HASH,
            plan.set.salt_bytes as u64,
            plan.set.nonce_bytes as u64,
            plan.set.position_bytes as u64,
            plan.set.samples as u64,
            plan.set.saved_coefficient as u64,
            plan.rounds.len() as u64,
        ] {
            parameters.put_u64(x);
        }
        for r in &plan.rounds {
            PublicBytes::public_bytes(&r.name, &mut parameters);
            for x in [
                r.count,
                r.work_bits as u64,
                r.message_bytes as u64,
                r.roots as u64,
                r.answers as u64,
                r.draw_e,
                r.draw_nonzero,
                r.draw_positions,
                r.log_n as u64,
                r.draw_trits,
                r.rows,
            ] {
                parameters.put_u64(x);
            }
        }
        Binder {
            label,
            plan,
            mark: Rc::new(0),
            earlier: Vec::new(),
            earlier_instances: Vec::new(),
            parameters,
            statement: Writer::default(),
            salted: true,
            salt_in_proof: true,
            has_configuration: false,
            other_items: false,
            salt: Digest::zero(),
            configuration: Digest::zero(),
            earlier_fates: Vec::new(),
            parameters_closed: false,
            closed: false,
        }
    }

    /// Appends a named value to the parameters (`parameter`).
    pub fn parameter<T: PublicBytes>(&mut self, name: &str, value: T) -> Public<T> {
        assert!(
            !self.parameters_closed,
            "binder: the parameters are closed by the first item of the statement and by the run's value"
        );
        self.other_items = true;
        self.item(true, name, value)
    }

    /// Appends a named value to the statement (`statement`).
    pub fn statement<T: PublicBytes>(&mut self, name: &str, value: T) -> Public<T> {
        assert!(!self.closed, "binder: the chain has begun: its first query takes nothing more");
        self.parameters_closed = true;
        self.item(false, name, value)
    }

    /// This chain follows an earlier chain of its session (`follows`).
    pub fn follows(&mut self, earlier: &Sealed) {
        self.statement("the seal of an earlier chain", *earlier.digest());
        self.earlier.extend(earlier.marks.iter().cloned());
        self.earlier_fates.extend(earlier.fates.iter().cloned());
        self.earlier_instances.push(earlier.instance);
    }

    /// A chain with no salt and no run's value (`no_random_bytes`).
    pub fn no_random_bytes(&mut self) {
        self.salted = false;
    }

    /// Both sides take the salt from `x`, a value bound by this Binder (`random_bytes_are`).
    pub fn random_bytes_are(&mut self, x: &Public<Digest>) {
        assert!(
            x.is_bound()
                && x.mark().is_some()
                && Rc::ptr_eq(x.mark().unwrap(), &self.mark),
            "binder: these bytes do not stand in this first query"
        );
        self.salt_in_proof = false;
        self.salt = *x.value().unwrap();
    }

    /// The configuration digest, the first item behind the plan (`configuration`).
    pub fn configuration(&mut self, digest: &Digest) -> Public<Digest> {
        assert!(!self.has_configuration, "binder: a chain names its configuration once");
        assert!(!self.other_items, "binder: the configuration is the first item behind the plan");
        self.has_configuration = true;
        self.configuration = *digest;
        self.parameter("configuration", *digest)
    }

    /// The named configuration digest (`configuration_digest`).
    pub fn configuration_digest(&self) -> Digest {
        assert!(
            self.has_configuration,
            "binder: every chain names its configuration, as the first item behind the plan"
        );
        for e in &self.earlier_instances {
            assert!(
                *e == self.configuration,
                "binder: two chains of one session name two configurations"
            );
        }
        self.configuration
    }

    pub fn plan(&self) -> Rc<Planned> {
        self.plan.clone()
    }
    pub fn parameter_bytes(&self) -> &[u8] {
        self.parameters.bytes()
    }
    pub fn statement_bytes(&self) -> &[u8] {
        self.statement.bytes()
    }

    /// The digest of the parameters list (`parameters_digest`).
    pub fn parameters_digest(&mut self, calls: &mut HashCalls) -> Digest {
        self.parameters_closed = true;
        let mut h = Hasher::new(&Tag::plain(Domain::Parameters, 0), 1, calls);
        h.push(self.parameters.bytes());
        h.finish()
    }

    /// Closes the Binder (`first_query`). `salt` is the prover's; a verifier passes zeros and
    /// reads the salt from the proof.
    pub(crate) fn first_query(&mut self, salt: &Digest, calls: &mut HashCalls) -> FirstQuery {
        self.closed = true;
        let parameters = self.parameters_digest(calls);
        FirstQuery {
            label: self.label,
            parameters,
            statement: self.statement.bytes().to_vec(),
            record: Vec::new(),
            salted: self.salted,
            salt_in_proof: self.salt_in_proof,
            salt: if self.salt_in_proof { *salt } else { self.salt },
        }
    }

    fn item<T: PublicBytes>(&mut self, parameter: bool, name: &str, value: T) -> Public<T> {
        assert!(value.public_fault().is_none(), "binder: a public value contradicts itself");
        let mut bytes = Writer::default();
        value.public_bytes(&mut bytes);
        let w = if parameter { &mut self.parameters } else { &mut self.statement };
        PublicBytes::public_bytes(&String::from(name), w);
        w.put_u64(bytes.size() as u64);
        w.put_bytes(bytes.bytes());
        Public::new(self.mark.clone(), value)
    }
}
