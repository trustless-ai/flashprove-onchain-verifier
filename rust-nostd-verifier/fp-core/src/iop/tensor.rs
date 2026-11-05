//! Coefficient vectors in structured form, ported from `blocks/iop/tensor.h` (lines 36-773).
//!
//! A `Tensor` is `scalar * prod_t (bit t of j ? hi[t] : lo[t])`, optionally times a slice of a
//! written-out vector; a `Form` is a sum of tensors and single entries. The C++ prover alone can
//! point a tensor or a form at a vector that only its engine holds (`Tensor::held`,
//! `EngineTerm`, `Held`); a verifier has no engine, so those fields and their functions are not
//! ported. Every function that would need such an entry in C++ panics here instead of reading it.
//! The verifier-visible arithmetic (tensors, entries, frozen parts, fold, evaluation) is ported in
//! full. Variables are numbered from the lowest bit of an index, as in the C++ header.

use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use crate::field::ext::{F, E};

/// Whether an element of E lies in F (`lies_in_F`, tensor.h:43).
#[inline]
pub fn lies_in_f(a: &E) -> bool {
    (a.0[1].0 | a.0[2].0) == 0
}

/// The C++ spelling of `lies_in_f`, for the block ports that keep the source's names.
#[allow(non_snake_case)]
#[inline]
pub fn lies_in_F(a: &E) -> bool {
    lies_in_f(a)
}

/// a * b, with one multiplication in F when b lies there (`times`, tensor.h:44).
#[inline]
pub fn times(a: &E, b: &E) -> E {
    if lies_in_f(b) {
        *a * b.0[0]
    } else {
        *a * *b
    }
}

/// sum += a * b, one coordinate at a time (`add_product`, tensor.h:45-47).
#[inline]
pub fn add_product(sum: &mut E, a: &E, b: F) {
    for i in 0..3 {
        sum.0[i] += a.0[i] * b;
    }
}

/// One variable's cached choice product (`Tensor::Picked`, tensor.h:228-231).
#[derive(Clone, Copy, Debug, Default)]
pub struct Picked {
    pub mask: u64,
    pub value: u64,
    pub product: E,
}

impl Picked {
    fn new() -> Self {
        Picked { mask: 0, value: 0, product: E::one() }
    }
}

/// A folded slice (`Tensor::Slice`, tensor.h:232-235).
#[derive(Clone, Debug)]
pub struct Slice {
    pub values: Option<Rc<Vec<E>>>,
    pub factor: E,
}

/// A coefficient vector in product form (`Tensor`, tensor.h:69-427).
#[derive(Clone, Debug)]
pub struct Tensor {
    pub scalar: E,
    /// The dense variables, which index the written-out slice (`dense_vars`).
    pub dense_vars: Vec<u32>,
    /// The slice (`values`). The port keeps `Rc` where C++ keeps `shared_ptr<const vector<E>>`.
    pub values: Option<Rc<Vec<E>>>,
    pub first: u64,
    pairs: Rc<Vec<E>>,
    from: usize,
    vars: u32,
    pick_mask: u64,
    pick_value: u64,
}

impl Default for Tensor {
    /// The C++ default has `scalar = E::one()` (tensor.h:70); the port keeps it.
    fn default() -> Self {
        Tensor {
            scalar: E::one(),
            dense_vars: Vec::new(),
            values: None,
            first: 0,
            pairs: Rc::new(Vec::new()),
            from: 0,
            vars: 0,
            pick_mask: 0,
            pick_value: 0,
        }
    }
}

impl Tensor {
    /// The constant tensor 0: a port helper, not a C++ constructor (C++ `Tensor()` has scalar one).
    pub fn zero() -> Self {
        Tensor { scalar: E::zero(), ..Tensor::default() }
    }
    /// The constant tensor 1 (`Tensor()` with `scalar = E::one()`).
    pub fn one() -> Self {
        Tensor { scalar: E::one(), ..Tensor::default() }
    }

    pub fn vars(&self) -> u32 {
        self.vars
    }
    pub fn has_dense(&self) -> bool {
        !self.dense_vars.is_empty()
    }
    /// A prover-only factor in an engine's table: no verifier tensor has one (`is_held`).
    pub fn is_held(&self) -> bool {
        false
    }
    pub fn picks(&self, t: u32) -> bool {
        (self.pick_mask >> t) & 1 != 0
    }
    pub fn pick_mask(&self) -> u64 {
        self.pick_mask
    }
    pub fn pick_value(&self) -> u64 {
        self.pick_value
    }
    /// The pair (lo, hi) of variable `t` (`lo`, `hi`, tensor.h:100-101).
    pub fn lo(&self, t: u32) -> E {
        if self.picks(t) {
            if (self.pick_value >> t) & 1 != 0 { E::zero() } else { E::one() }
        } else {
            self.pairs[2 * self.real_at(t)]
        }
    }
    pub fn hi(&self, t: u32) -> E {
        if self.picks(t) {
            if (self.pick_value >> t) & 1 != 0 { E::one() } else { E::zero() }
        } else {
            self.pairs[2 * self.real_at(t) + 1]
        }
    }
    pub fn los(&self) -> Vec<E> {
        (0..self.vars).map(|t| self.lo(t)).collect()
    }
    pub fn his(&self) -> Vec<E> {
        (0..self.vars).map(|t| self.hi(t)).collect()
    }
    /// The pairs of the real variables, lowest first (`real_pairs`, tensor.h:120).
    pub fn real_pairs(&self) -> &[E] {
        let at = 2 * self.from;
        &self.pairs[at..at + 2 * self.reals()]
    }

    /// The equality vector eq(., z), on the first `a` coordinates (`eq`, tensor.h:122-127).
    pub fn eq(z: &[E], a: u32, scalar: E) -> Self {
        let mut v = Tensor { scalar, ..Tensor::default() };
        for t in 0..a {
            let zt = z[t as usize];
            v.push(E::one() - zt, zt);
        }
        v
    }

    /// The same over every coordinate of `z`.
    pub fn eq_all(z: &[E], scalar: E) -> Self {
        Tensor::eq(z, z.len() as u32, scalar)
    }
    /// lo = 1, hi = f[t], on the first `a` entries (`product`, tensor.h:129-134).
    pub fn product(f: &[F], a: u32, scalar: E) -> Self {
        let mut v = Tensor { scalar, ..Tensor::default() };
        for t in 0..a {
            v.push(E::one(), E::from_base(f[t as usize]));
        }
        v
    }

    /// Appends the new highest variable (`push`, tensor.h:136-148).
    pub fn push(&mut self, l: E, h: E) {
        assert!(self.vars < 63, "tensor: more than 63 variables");
        let l0 = l.is_zero();
        let h0 = h.is_zero();
        if (l0 && h == E::one()) || (h0 && l == E::one()) {
            self.pick_mask |= 1u64 << self.vars;
            if l0 {
                self.pick_value |= 1u64 << self.vars;
            }
        } else {
            self.own_pairs();
            let p = Rc::get_mut(&mut self.pairs).unwrap();
            p.push(l);
            p.push(h);
        }
        self.vars += 1;
    }

    /// Replaces the pair of variable `t` (`set_pair`, tensor.h:150-154).
    pub fn set_pair(&mut self, t: u32, l: E, h: E) {
        let mut los = Vec::with_capacity(self.vars as usize);
        let mut his = Vec::with_capacity(self.vars as usize);
        for i in 0..self.vars {
            los.push(if i == t { l } else { self.lo(i) });
            his.push(if i == t { h } else { self.hi(i) });
        }
        self.rebuild(&los, &his);
    }

    /// Moves the first `by` variables behind the others (`rotate`, tensor.h:156-161). The dense
    /// variables are left to the caller, as in C++.
    pub fn rotate(&mut self, by: u32) {
        let mut los = Vec::with_capacity(self.vars as usize);
        let mut his = Vec::with_capacity(self.vars as usize);
        for i in 0..self.vars {
            let t = (i + by) % self.vars;
            los.push(self.lo(t));
            his.push(self.hi(t));
        }
        self.rebuild(&los, &his);
    }

    /// Appends `count` dense variables (`push_dense`, tensor.h:163-167).
    pub fn push_dense(&mut self, count: u32) {
        assert!(!self.has_dense(), "tensor: a dense variable is added after the slice was fixed");
        for _ in 0..count {
            self.dense_vars.push(self.vars);
            self.push(E::one(), E::one());
        }
    }

    /// Sets the dense slice (`set_values`, tensor.h:169-173).
    pub fn set_values(&mut self, values: Rc<Vec<E>>, first: u64) {
        assert!(
            !self.dense_vars.is_empty(),
            "tensor: a slice for a tensor without dense variables"
        );
        self.dense_check(first, values.len() as u64);
        self.values = Some(values);
        self.first = first;
    }

    /// Inserts choice variables before `at` (`insert_choice`, tensor.h:195-205).
    pub fn insert_choice(&mut self, at: u32, count: u32, value: u64) {
        assert!(at <= self.vars, "tensor: no such variable");
        assert!(count <= 63 && self.vars + count <= 63, "tensor: more than 63 variables");
        if count == 0 {
            return;
        }
        let low = (1u64 << at) - 1;
        let ones = (1u64 << count) - 1;
        self.pick_mask = (self.pick_mask & low) | ((self.pick_mask & !low) << count) | (ones << at);
        self.pick_value = (self.pick_value & low) | ((self.pick_value & !low) << count) | ((value & ones) << at);
        self.vars += count;
        for d in &mut self.dense_vars {
            if *d >= at {
                *d += count;
            }
        }
    }

    /// The entry at index `j` (`at`, tensor.h:207-217).
    pub fn at(&self, j: u64) -> E {
        self.factor_check();
        if (j & self.pick_mask) != self.pick_value {
            return E::zero();
        }
        let mut r = self.scalar;
        let mut pair = self.from;
        for t in 0..self.vars {
            if !self.picks(t) {
                r = r * self.pairs[2 * pair + ((j >> t) & 1) as usize];
                pair += 1;
            }
        }
        if !self.has_dense() || r.is_zero() {
            return r;
        }
        r * self.values.as_ref().unwrap()[(self.first + self.dense_index(j)) as usize]
    }

    /// The multilinear extension at `x` (`mle`, tensor.h:219-224).
    pub fn mle(&self, x: &[E]) -> E {
        let mut v = self.clone();
        v.fix_low(x, v.vars());
        v.scalar
    }

    /// Whether one of the first `count` variables is dense (`slice_is_cut`, tensor.h:275-279).
    pub fn slice_is_cut(&self, count: u32) -> bool {
        self.dense_vars.iter().any(|&d| d < count)
    }

    /// Folds the first `count` variables at `g` (`fix_low`, tensor.h:238-273).
    pub fn fix_low(&mut self, g: &[E], count: u32) {
        let mut last = Picked::new();
        self.fix_low_with(g, count, &mut last, None);
    }

    /// The same with the cache and an optional pre-folded slice (`fix_low`, tensor.h:244-273).
    pub fn fix_low_with(&mut self, g: &[E], count: u32, last: &mut Picked, ready: Option<&Slice>) {
        assert!(count <= self.vars, "tensor: more variables fixed than there are");
        self.factor_check();
        let low = (1u64 << count) - 1;
        let mask = self.pick_mask & low;
        let value = self.pick_value & low;
        if mask != last.mask || value != last.value {
            last.mask = mask;
            last.value = value;
            last.product = E::one();
            for t in 0..count {
                if (mask >> t) & 1 != 0 {
                    last.product = last.product * if (value >> t) & 1 != 0 { g[t as usize] } else { E::one() - g[t as usize] };
                }
            }
        }
        if mask != 0 {
            self.scalar = self.scalar * last.product;
        }
        for t in 0..count {
            if (mask >> t) & 1 != 0 {
                continue;
            }
            let l = self.pairs[2 * self.from];
            let h = self.pairs[2 * self.from + 1];
            self.from += 1;
            if l == E::one() && h == E::one() {
                continue;
            }
            self.scalar = self.scalar * (l + g[t as usize] * (h - l));
        }
        self.pick_mask >>= count;
        self.pick_value >>= count;
        self.vars -= count;
        if !self.has_dense() {
            return;
        }
        if self.slice_is_cut(count) {
            let s = match ready {
                Some(s) => s.clone(),
                None => self.folded_slice(g, count),
            };
            self.dense_vars.retain(|&d| d >= count);
            if self.dense_vars.is_empty() {
                self.scalar = self.scalar * s.factor;
                self.values = None;
            } else {
                self.values = s.values;
            }
            self.first = 0;
        }
        for d in &mut self.dense_vars {
            *d -= count;
        }
    }

    /// The dense factor after the first `count` variables are fixed (`folded_slice`, tensor.h:287-310).
    pub fn folded_slice(&self, g: &[E], count: u32) -> Slice {
        let mut room = Vec::new();
        self.folded_slice_into(g, count, &mut room)
    }
    /// The same with a caller's scratch buffer (`folded_slice`, tensor.h:287-310).
    pub fn folded_slice_into(&self, g: &[E], count: u32, room: &mut Vec<E>) -> Slice {
        assert!(self.values.is_some(), "tensor: dense variables without a vector");
        let values = self.values.as_ref().unwrap();
        let mut n = 1usize << self.dense_vars.len();
        assert!(
            self.first <= values.len() as u64 && n <= values.len() - self.first as usize,
            "tensor: a written-out slice reaches beyond its vector"
        );
        let mut cur: Vec<E> = values[self.first as usize..self.first as usize + n].to_vec();
        for i in (0..self.dense_vars.len()).rev() {
            if self.dense_vars[i] >= count {
                continue;
            }
            let x = g[self.dense_vars[i] as usize];
            let low_half = 1usize << i;
            let half = n / 2;
            // The fold is done in place: every write lands below `half`, and every later read is
            // at or above the write region (the reads of the current block happen first). The
            // caller's `room` is kept for the API that C++ has, and is no longer needed here.
            let _ = &room;
            for b in 0..n / (2 * low_half) {
                for a in 0..low_half {
                    let zero = cur[a + 2 * low_half * b];
                    let one = cur[a + low_half + 2 * low_half * b];
                    cur[a + low_half * b] = zero + (one - zero) * x;
                }
            }
            n = half;
            cur.truncate(n);
        }
        let factor = if n == 1 { cur[0] } else { E::one() };
        Slice { values: Some(Rc::new(cur)), factor }
    }

    /// Adds all entries to `out` (`add_to`, tensor.h:320-346).
    pub fn add_to(&self, out: &mut [E], room: &mut Vec<E>) {
        self.factor_check();
        let real = self.reals();
        let n = 1usize << real;
        if room.len() < n {
            room.resize(n, E::zero());
        }
        room[0] = self.scalar;
        for r in 0..real {
            let half = 1usize << r;
            let l = self.pairs[2 * (self.from + r)];
            let h = self.pairs[2 * (self.from + r) + 1];
            if l == E::one() && h == E::one() {
                for j in 0..half {
                    room[j + half] = room[j];
                }
            } else {
                spread(&mut room[..2 * half], half, l, h);
            }
        }
        let places = !self.pick_mask & ((1u64 << self.vars) - 1);
        let mut at = 0u64;
        for j in 0..n {
            let index = at | self.pick_value;
            let value = if self.has_dense() {
                room[j] * self.values.as_ref().unwrap()[(self.first + self.dense_index(index)) as usize]
            } else {
                room[j]
            };
            out[index as usize] += value;
            at = at.wrapping_sub(places) & places;
        }
    }
    pub fn add_to_simple(&self, out: &mut [E]) {
        let mut room = Vec::new();
        self.add_to(out, &mut room);
    }

    /// The factor on variables `from .. from + count` (`part`, tensor.h:354-376).
    pub fn part(&self, from: u32, count: u32) -> Vec<E> {
        assert!(from <= self.vars && count <= self.vars - from, "tensor: a part beyond the variables");
        let mut w = vec![E::zero(); 1usize << count];
        w[0] = E::one();
        for t in 0..count {
            let half = 1usize << t;
            if self.picks(from + t) {
                let one = (self.pick_value >> (from + t)) & 1 != 0;
                for j in 0..half {
                    w[j + half] = if one { w[j] } else { E::zero() };
                }
                if one {
                    for j in 0..half {
                        w[j] = E::zero();
                    }
                }
                continue;
            }
            let l = self.lo(from + t);
            let h = self.hi(from + t);
            if l == E::one() && h == E::one() {
                for j in 0..half {
                    w[j + half] = w[j];
                }
            } else {
                spread(&mut w[..2 * half], half, l, h);
            }
        }
        w
    }

    fn factor_check(&self) {
        assert!(
            self.dense_vars.is_empty() || self.values.is_some(),
            "tensor: dense variables without a vector"
        );
    }
    fn dense_check(&self, first_: u64, length: u64) {
        assert!(
            self.dense_vars.len() < 64 && first_ <= length && (1u64 << self.dense_vars.len()) <= length - first_,
            "tensor: the slice does not lie in the vector"
        );
        for i in 0..self.dense_vars.len() {
            let d = self.dense_vars[i];
            assert!(d < self.vars && self.lo(d) == E::one() && self.hi(d) == E::one(), "tensor: a dense variable does not exist, or has another pair than (1, 1)");
            for j in 0..i {
                assert!(self.dense_vars[i] != self.dense_vars[j], "tensor: a variable is dense twice");
            }
        }
    }
    fn dense_index(&self, j: u64) -> u64 {
        let mut d = 0u64;
        for i in 0..self.dense_vars.len() {
            d |= ((j >> self.dense_vars[i]) & 1) << i;
        }
        d
    }
    fn real_at(&self, t: u32) -> usize {
        self.from + ((!self.pick_mask & ((1u64 << t) - 1)).count_ones() as usize)
    }
    fn reals(&self) -> usize {
        self.vars as usize - self.pick_mask.count_ones() as usize
    }
    fn own_pairs(&mut self) {
        if self.pairs.is_empty() && Rc::strong_count(&self.pairs) == 1 {
            // A fresh empty list, as in C++ when pairs_ is null.
            self.from = 0;
            return;
        }
        let want = 2 * (self.from + self.reals());
        if Rc::strong_count(&self.pairs) > 1 || self.pairs.len() != want {
            let from = self.from;
            self.pairs = Rc::new(self.pairs[2 * from..2 * from + want].to_vec());
            self.from = 0;
        }
    }
    fn rebuild(&mut self, los: &[E], his: &[E]) {
        self.pairs = Rc::new(Vec::new());
        self.from = 0;
        self.vars = 0;
        self.pick_mask = 0;
        self.pick_value = 0;
        for i in 0..los.len() {
            self.push(los[i], his[i]);
        }
    }
}

fn spread(v: &mut [E], half: usize, l: E, h: E) {
    let l_is_one = l == E::one();
    let one_less_h = l + h == E::one();
    if l_is_one {
        for j in 0..half {
            v[j + half] = v[j] * h;
        }
    } else if one_less_h {
        for j in 0..half {
            v[j + half] = v[j] * h;
            v[j] = v[j] - v[j + half];
        }
    } else {
        for j in 0..half {
            v[j + half] = v[j] * h;
            v[j] = v[j] * l;
        }
    }
}

/// A long part stored once (`FrozenPart`, tensor.h:463-469).
#[derive(Clone, Debug)]
pub struct FrozenPart {
    pub form: Rc<Form>,
    pub vars: u32,
    pub scale: E,
    pub choice_mask: u64,
    pub choice_value: u64,
}

/// A coefficient vector: sum of tensors, entries, frozen parts (`Form`, tensor.h:475-755).
#[derive(Clone, Debug, Default)]
pub struct Form {
    pub tensors: Vec<Tensor>,
    pub entries: Vec<(u64, E)>,
    pub frozen: Vec<FrozenPart>,
}

impl Form {
    pub fn empty(&self) -> bool {
        self.tensors.is_empty() && self.entries.is_empty() && self.frozen.is_empty()
    }

    /// Turns the whole form into one frozen part (`freeze`, tensor.h:484-493).
    pub fn freeze(&mut self, vars: u32) {
        assert!(self.fits(vars), "form: a part does not fit a vector of this many variables");
        let mut all = Form::default();
        core::mem::swap(&mut all.tensors, &mut self.tensors);
        core::mem::swap(&mut all.entries, &mut self.entries);
        core::mem::swap(&mut all.frozen, &mut self.frozen);
        self.frozen.push(FrozenPart { form: Rc::new(all), vars, scale: E::one(), choice_mask: 0, choice_value: 0 });
    }

    /// The same vector, with frozen parts copied out (`flattened`, tensor.h:495-499).
    pub fn flattened(&self) -> Form {
        let mut f = self.clone();
        f.thaw();
        f
    }

    /// `flattened()`, in place (`thaw`, tensor.h:501-511).
    pub fn thaw(&mut self) {
        let mut parts = Vec::new();
        core::mem::swap(&mut parts, &mut self.frozen);
        for p in parts {
            let mut f = p.form.flattened();
            for t in 0..64 {
                if (p.choice_mask >> t) & 1 != 0 {
                    f.insert_choice(t, 1, (p.choice_value >> t) & 1);
                }
            }
            for mut v in f.tensors {
                v.scalar = v.scalar * p.scale;
                self.tensors.push(v);
            }
            for (i, c) in f.entries {
                self.entries.push((i, c * p.scale));
            }
        }
    }

    /// Appends a tensor (`Form::add(Tensor)`, tensor.h:520).
    pub fn add(&mut self, v: Tensor) {
        self.tensors.push(v);
    }

    /// The same under a name that cannot be confused with the `&Form` form.
    pub fn push_tensor(&mut self, v: Tensor) {
        self.tensors.push(v);
    }

    /// Whether a tensor points at an engine's table (`has_held_factor`): never in the verifier.
    pub fn has_held_factor(&self) -> bool {
        false
    }
    pub fn add_entry(&mut self, index: u64, coefficient: E) {
        self.entries.push((index, coefficient));
    }

    /// this += x * other; clones the other (`add(const Form&, x)`, tensor.h:522-535).
    pub fn add_ref(&mut self, other: &Form, x: E) {
        assert!(!core::ptr::eq(other, self), "form: a form is added to itself");
        let t0 = self.tensors.len();
        let e0 = self.entries.len();
        for v in &other.tensors {
            let mut v = v.clone();
            v.scalar = v.scalar * x;
            self.tensors.push(v);
        }
        for &(i, c) in &other.entries {
            self.entries.push((i, c * x));
        }
        for p in &other.frozen {
            let mut p = p.clone();
            p.scale = p.scale * x;
            self.frozen.push(p);
        }
        let _ = (t0, e0);
    }

    /// this += x * other, moving its parts (`add(Form&&, x)`, tensor.h:536-553). The Rust caller
    /// passes the form by value.
    pub fn add_owned(&mut self, other: Form, x: E) {
        let t0 = self.tensors.len();
        let e0 = self.entries.len();
        for mut v in other.tensors {
            v.scalar = v.scalar * x;
            self.tensors.push(v);
        }
        for (i, c) in other.entries {
            self.entries.push((i, c * x));
        }
        for mut p in other.frozen {
            p.scale = p.scale * x;
            self.frozen.push(p);
        }
        let _ = (t0, e0);
    }

    pub fn scale(&mut self, x: E) {
        for v in &mut self.tensors {
            v.scalar = v.scalar * x;
        }
        for e in &mut self.entries {
            e.1 = e.1 * x;
        }
        for p in &mut self.frozen {
            p.scale = p.scale * x;
        }
    }

    /// The entry at index `j` (`at`, tensor.h:561-571).
    pub fn at(&self, j: u64) -> E {
        let mut r = E::zero();
        for v in &self.tensors {
            r += v.at(j);
        }
        for &(i, c) in &self.entries {
            if i == j {
                r += c;
            }
        }
        for p in &self.frozen {
            if (j & p.choice_mask) == p.choice_value {
                r += p.scale * p.form.at(without_bits(j, p.choice_mask));
            }
        }
        r
    }

    /// The index formed by the bits of `j` outside `mask`, in order (`without_bits`, tensor.h:572-578).
    pub fn without_bits(j: u64, mask: u64) -> u64 {
        without_bits(j, mask)
    }

    /// The multilinear extension at `x` (`mle`, tensor.h:579-585).
    pub fn mle(&self, x: &[E], vars: u32) -> E {
        assert!(self.fits(vars), "form: a part does not fit a vector of this many variables");
        let mut f = self.clone();
        f.fix_low(x, vars, E::one());
        f.at(0)
    }

    /// Fixes the first `count` variables at `g`, then multiplies by `times`
    /// (`fix_low`, tensor.h:589-640).
    pub fn fix_low(&mut self, g: &[E], count: u32, times: E) {
        let scaled = times != E::one();
        {
            let low = (1u64 << count) - 1;
            let mut all_choices = true;
            for p in &self.frozen {
                all_choices = all_choices && (p.choice_mask & low) == low;
            }
            if !all_choices {
                self.thaw();
            }
            for p in &mut self.frozen {
                for t in 0..count {
                    p.scale = p.scale * if (p.choice_value >> t) & 1 != 0 { g[t as usize] } else { E::one() - g[t as usize] };
                }
                if scaled {
                    p.scale = p.scale * times;
                }
                p.choice_mask >>= count;
                p.choice_value >>= count;
            }
        }
        // Each distinct slice that is cut is folded once (Tensor::folded_slice()).
        let mut number = alloc::collections::BTreeMap::new();
        let mut slice_of = vec![usize::MAX; self.tensors.len()];
        let mut first_with: Vec<usize> = Vec::new();
        for i in 0..self.tensors.len() {
            let v = &self.tensors[i];
            if !v.has_dense() || !v.slice_is_cut(count) {
                continue;
            }
            assert!(v.values.is_some(), "tensor: dense variables without a vector");
            let key = (
                Rc::as_ptr(v.values.as_ref().unwrap()) as usize,
                v.first,
                v.dense_vars.clone(),
            );
            let at = match number.get(&key) {
                Some(&x) => x,
                None => {
                    let x = first_with.len();
                    number.insert(key, x);
                    first_with.push(i);
                    x
                }
            };
            slice_of[i] = at;
        }
        let mut folded: Vec<Slice> = Vec::with_capacity(first_with.len());
        let mut room = Vec::new();
        for &i in &first_with {
            folded.push(self.tensors[i].folded_slice_into(g, count, &mut room));
        }
        let mut last = Picked::new();
        for i in 0..self.tensors.len() {
            let mut v = core::mem::take(&mut self.tensors[i]);
            if scaled {
                v.scalar = v.scalar * times;
            }
            let ready = if slice_of[i] == usize::MAX { None } else { Some(&folded[slice_of[i]]) };
            v.fix_low_with(g, count, &mut last, ready);
            self.tensors[i] = v;
        }
        if count <= 12 && self.entries.len() > (1usize << count) {
            let mut weight = vec![E::one(); 1usize << count];
            for t in 0..count {
                for j in 0..(1usize << t) {
                    weight[j | (1usize << t)] = weight[j] * g[t as usize];
                    weight[j] = weight[j] * (E::one() - g[t as usize]);
                }
            }
            for w in &mut weight {
                *w = *w * times;
            }
            for e in &mut self.entries {
                e.1 = e.1 * weight[(e.0 & ((1u64 << count) - 1)) as usize];
                e.0 >>= count;
            }
        } else {
            for e in &mut self.entries {
                for t in 0..count {
                    e.1 = e.1 * if (e.0 >> t) & 1 != 0 { g[t as usize] } else { E::one() - g[t as usize] };
                }
                e.1 = e.1 * times;
                e.0 >>= count;
            }
        }
        self.merge_entries();
    }

    /// Merges entries with one index and sorts (`merge_entries`, tensor.h:643-694).
    pub fn merge_entries(&mut self) {
        if self.entries.len() < 2 {
            return;
        }
        self.entries.sort_by(|a, b| a.0.cmp(&b.0).then(Ordering::Equal));
        let old = core::mem::take(&mut self.entries);
        let mut n = 0usize;
        for (i, c) in old {
            if n > 0 && self.entries[n - 1].0 == i {
                self.entries[n - 1].1 += c;
            } else {
                self.entries.push((i, c));
                n += 1;
            }
        }
    }

    /// Inserts choice variables before `at` (`insert_choice`, tensor.h:696-714).
    pub fn insert_choice(&mut self, at: u32, count: u32, value: u64) {
        assert!(at + count < 64 && value >> count == 0, "form: the value has more bits than are inserted, or an index would pass 63 bits");
        let low = (1u64 << at) - 1;
        let widen = |j: u64| (j & low) | ((j & !low) << count);
        for v in &mut self.tensors {
            v.insert_choice(at, count, value);
        }
        for e in &mut self.entries {
            e.0 = widen(e.0) | (value << at);
        }
        for p in &mut self.frozen {
            p.choice_mask = widen(p.choice_mask) | (((1u64 << count) - 1) << at);
            p.choice_value = widen(p.choice_value) | (value << at);
        }
    }

    /// Adds all entries to `out` (`add_to`, tensor.h:716-738).
    pub fn add_to(&self, out: &mut [E], vars: u32) {
        let mut room = Vec::new();
        for v in &self.tensors {
            assert!(v.vars() == vars, "form: a tensor with another number of variables");
            v.add_to(out, &mut room);
        }
        for &(i, c) in &self.entries {
            assert!(i >> vars == 0, "form: an entry beyond the vector's length");
            out[i as usize] += c;
        }
        for p in &self.frozen {
            assert!(frozen_fits(p, vars), "form: a frozen part with another number of variables");
            let mut inner = vec![E::zero(); 1usize << p.vars];
            p.form.add_to(&mut inner, p.vars);
            for j in 0..(1u64 << vars) {
                if (j & p.choice_mask) == p.choice_value {
                    out[j as usize] += p.scale * inner[without_bits(j, p.choice_mask) as usize];
                }
            }
        }
    }

    /// Whether every part fits a vector of `2^vars` entries (`fits`, tensor.h:744-754).
    pub fn fits(&self, vars: u32) -> bool {
        for p in &self.frozen {
            if !frozen_fits(p, vars) {
                return false;
            }
        }
        for v in &self.tensors {
            if v.vars() != vars {
                return false;
            }
        }
        for &(i, _) in &self.entries {
            if vars < 64 && i >> vars != 0 {
                return false;
            }
        }
        true
    }
}

fn frozen_fits(p: &FrozenPart, vars: u32) -> bool {
    vars < 64 && p.choice_mask >> vars == 0 && p.vars + p.choice_mask.count_ones() == vars
}

fn without_bits(j: u64, mask: u64) -> u64 {
    let mut inner = 0u64;
    let mut i = 0u32;
    for t in 0..64 {
        if (mask >> t) & 1 == 0 {
            inner |= ((j >> t) & 1) << i;
            i += 1;
        }
    }
    inner
}

/// Entry `j` of `scale * w` under choice variables, for a written-out `w`
/// (`under_choices_at`, tensor.h:758-765). Exposed for the block tests and later ports.
pub fn under_choices_at(scale: E, choice_mask: u64, choice_value: u64, w: &[E], j: u64, vars: u32) -> E {
    if (j & choice_mask) != choice_value {
        return E::zero();
    }
    let mut inner = 0u64;
    let mut i = 0u32;
    for t in 0..vars {
        if (choice_mask >> t) & 1 == 0 {
            inner |= ((j >> t) & 1) << i;
            i += 1;
        }
    }
    assert!((inner as usize) < w.len(), "form: a vector that the engine holds is shorter than the form says");
    scale * w[inner as usize]
}
