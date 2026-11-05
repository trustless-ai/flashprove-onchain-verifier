//! The stage's parameter statement and the layer layout, ported from the first half of
//! `verifier/src/cp_verify.cpp` (`polPrescan`, `polSkeleton`, `polScan`, `parseHeader`, `layout`).
//!
//! This is the context that the layer and output-head sub-proofs use: the model's statement
//! (`Hdr`), the layout of the four request matrices (`Lay`, `Ten`, `CallD`, `Seg`) and the lookup
//! forest of the layer sub-proof. It reads no proof.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use crate::consts::{LIDB_MAX, LIDB_SEALED, NMINH_MAX};
use crate::frame::parameters::{read_parameters, Parameters};
use crate::hash::earlier::DW;
use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};
use crate::stage_state::StageState;

use super::attention_shape::{ten_cell, TenAt};
use super::common::{admit_word, WORK_BITS_MOST};
use super::lookup::{forest_plane_cols, forest_pub_ask, forest_shape, HForest};
use super::tables::{gate_table_entry, sigmoid_clamp_table_entry, TableParams};

/// The classes of rounded matrix products (`enum` kq_ .. kdM).
pub const KQ_: usize = 0;
pub const KK_: usize = 1;
pub const KV_: usize = 2;
pub const KO_: usize = 3;
pub const KGD: usize = 4;
pub const KUD: usize = 5;
pub const KDD: usize = 6;
pub const KR_: usize = 7;
pub const KGS: usize = 8;
pub const KUS: usize = 9;
pub const KGR: usize = 10;
pub const KUR: usize = 11;
pub const KDM: usize = 12;

/// The statement's length in words.
pub const fn statement_length_words() -> usize {
    29 + DW + 34 + 4 * DW + 11 + 2 * DW + 25 + 2 * DW + 1 + 1 + 4
}

/// The statement as parsed (`struct Hdr`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Hdr {
    pub ver: u32,
    pub at_w: usize,
    pub off_a: usize,
    pub prof: u32,
    pub lt: u32,
    pub l: u32,
    pub ll: u32,
    pub d: u64,
    pub h: u64,
    pub gk: u64,
    pub dh: u64,
    pub f: u64,
    pub fe: u64,
    pub ne: u64,
    pub v: u64,
    pub eps: [u64; 2],
    pub cs: u32,
    pub theta0: u64,
    pub hf: [u32; 13],
    pub ut: u32,
    pub h_calls: [u32; DW],
    /// The word offset of `h_calls` in the statement (the C++ pointer `h.hCalls - st.data()`).
    pub off_h_calls: usize,
    pub la: u32,
    pub nmin: u32,
    pub dd: u64,
    pub tau: u32,
    pub lmaf: u32,
    pub naf: u32,
    pub lmad: u32,
    pub nad: u32,
    pub lmar: u32,
    pub lmb: u32,
    pub lmq: u32,
    pub lmx: u32,
    pub wb: [u32; 12],
    pub iota: [u32; 8],
    pub h_ts: [u32; DW],
    pub h_sig: [u32; DW],
    pub h_rope: [u32; DW],
    pub h_kv: [u32; DW],
    /// The word offset of `h_ts` in the statement (the four arrays follow one another).
    pub off_h_ts: usize,
    pub off_eh: usize,
    pub l_b: u32,
    pub sx: u32,
    pub rx: u32,
    pub kfm: u32,
    pub kfd: u32,
    pub lms: u32,
    pub nas: u32,
    pub lmh: u32,
    pub lmo: u32,
    pub lmba: u32,
    pub iotaa0: u32,
    pub h_texp: [u32; DW],
    pub h_calls_a: [u32; DW],
    /// The word offsets of `h_texp` and `h_calls_a` in the statement.
    pub off_h_texp: usize,
    pub off_h_calls_a: usize,
    pub mf: u32,
    pub kf: u32,
    pub epsf: u64,
    pub toksrc: u32,
    pub lmhf: u32,
    pub nhf: u32,
    pub lmhd: u32,
    pub lmhr: u32,
    pub lmbh: u32,
    pub wbh: [u32; 2],
    pub iotah: [u32; 6],
    pub clipc: u32,
    pub theta: u32,
    pub cap: u32,
    pub logs: u32,
    pub digsh: u32,
    pub tabs: u32,
    pub famf: u32,
    pub h_calls_h: [u32; DW],
    /// The word offset of `h_calls_h` in the statement.
    pub off_h_calls_h: usize,
    pub h_tok: [u32; DW],
    pub ytok: u32,
    /// The word offset of `hTok` in the statement (the C++ pointer `h.hTok - st.data()`).
    pub off_h_tok: usize,
}

/// The caller's request (`struct StOwn`), reduced to what the layout's statement needs.
#[derive(Clone, Debug, Default)]
pub struct StOwn {
    pub hv: bool,
    pub hp: bool,
    pub hl: bool,
    pub ht: bool,
    pub pv: u64,
    pub pp: u64,
    pub plt: u64,
    pub pts: u64,
    pub r: u32,
    pub e: u32,
    pub y: u32,
    pub req: Vec<u32>,
    pub tok: Vec<u32>,
    pub laid: Vec<bool>,
}

/// `LineIterator`: the lines of a byte buffer, newline included. `Err(2)`: over 1023 bytes;
/// `Err(3)`: a zero byte.
pub struct LineIter<'a> {
    s: &'a [u8],
    p: usize,
}

impl<'a> LineIter<'a> {
    pub fn new(s: &'a [u8]) -> Self {
        Self { s, p: 0 }
    }
    pub fn next_line(&mut self, cap: usize) -> core::result::Result<Option<&'a [u8]>, i32> {
        if self.p >= self.s.len() {
            return Ok(None);
        }
        let n = match self.s[self.p..].iter().position(|&c| c == b'\n') {
            Some(i) => i + 1,
            None => self.s.len() - self.p,
        };
        if n > cap - 1 {
            return Err(2);
        }
        let line = &self.s[self.p..self.p + n];
        self.p += n;
        if line.contains(&0) {
            return Err(3);
        }
        Ok(Some(line))
    }
}

/// `wordLineForm`: the canonical form of a value line.
pub fn word_line_form(l: &[u8]) -> bool {
    let mut i = 0usize;
    while i < l.len() && l[i] > b' ' && l[i] < 127 {
        i += 1;
    }
    if i == 0 || i >= l.len() || l[i] != b' ' {
        return false;
    }
    i += 1;
    if i >= l.len() || !l[i].is_ascii_digit() {
        return false;
    }
    if l[i] == b'0' && (i + 1 >= l.len() || l[i + 1] != b'\n') {
        return false;
    }
    let d0 = i;
    let mut v = 0u64;
    while i < l.len() && l[i].is_ascii_digit() {
        if i - d0 >= 10 {
            return false;
        }
        v = 10 * v + (l[i] - b'0') as u64;
        i += 1;
    }
    v <= 0xFFFF_FFFF && i + 1 == l.len() && l[i] == b'\n'
}

/// `digitsBeyondScan`: more than 19 digits in a row.
pub fn digits_beyond_scan(l: &[u8]) -> bool {
    let mut run = 0;
    for &c in l {
        run = if c.is_ascii_digit() { run + 1 } else { 0 };
        if run > 19 {
            return true;
        }
    }
    false
}

/// The `sscanf("%63s %llu %7s", ...) == 2` test.
pub fn scanned(line: &[u8]) -> Option<(String, u64)> {
    let mut i = 0;
    while i < line.len() && (line[i] as char).is_whitespace() {
        i += 1;
    }
    let start = i;
    while i < line.len() && !(line[i] as char).is_whitespace() {
        i += 1;
    }
    if i == start {
        return None;
    }
    let name = core::str::from_utf8(&line[start..i]).ok()?.to_string();
    while i < line.len() && (line[i] as char).is_whitespace() {
        i += 1;
    }
    let vstart = i;
    while i < line.len() && line[i].is_ascii_digit() {
        i += 1;
    }
    if i == vstart {
        return None;
    }
    let mut v = 0u64;
    for &c in &line[vstart..i] {
        v = v.checked_mul(10)?.checked_add((c - b'0') as u64)?;
    }
    // A third token makes sscanf return 3, not 2.
    while i < line.len() && (line[i] as char).is_whitespace() {
        i += 1;
    }
    if i != line.len() {
        return None;
    }
    Some((name, v))
}

/// `polWord`: the first line `name <digits>` of the tail.
pub fn pol_word(rest: &[u8], name: &str) -> Option<u64> {
    let l = name.len();
    let mut a = 0usize;
    while a < rest.len() {
        let e = rest[a..].iter().position(|&c| c == b'\n').map(|i| a + i).unwrap_or(rest.len());
        if e - a > l + 1 && rest[a..a + l] == *name.as_bytes() && rest[a + l] == b' ' {
            if e - a - l - 1 > 10 {
                return None;
            }
            let mut v = 0u64;
            for &c in &rest[a + l + 1..e] {
                if !c.is_ascii_digit() {
                    return None;
                }
                v = 10 * v + (c - b'0') as u64;
            }
            return Some(v);
        }
        a = e + 1;
    }
    None
}

/// `parseHeader`: the statement, complete or partly written. Sets `statedTarget`.
pub fn parse_header(st: &[u32], state: &mut StageState) -> Result<Hdr> {
    if st.len() < 3 {
        return Err(Refusal::named("statement-length"));
    }
    let mut h = Hdr::default();
    let mut p = 0usize;
    let nx = |p: &mut usize| -> u32 {
        let v = st[*p];
        *p += 1;
        v
    };
    let nx2 = |p: &mut usize, st: &[u32]| -> u64 {
        let v = (st[*p] as u64) | ((st[*p + 1] as u64) << 32);
        *p += 2;
        v
    };
    if nx(&mut p) != 0x4D36_3100 {
        return Err(Refusal::named("header-magic"));
    }
    let ver = nx(&mut p);
    if !admit_word(state, ver) {
        return Err(Refusal::named("header-version"));
    }
    h.ver = ver;
    h.prof = nx(&mut p);
    if h.prof >> 4 != 1 {
        return Err(Refusal::named("policy-profile"));
    }
    h.prof &= 15;
    if st.len() != statement_length_words() {
        return Err(Refusal::named("statement-length"));
    }
    h.lt = nx(&mut p);
    h.l = nx(&mut p);
    h.ll = nx(&mut p);
    h.d = nx(&mut p) as u64;
    h.h = nx(&mut p) as u64;
    h.gk = nx(&mut p) as u64;
    h.dh = nx(&mut p) as u64;
    h.f = nx(&mut p) as u64;
    h.fe = nx(&mut p) as u64;
    h.ne = nx(&mut p) as u64;
    h.v = nx(&mut p) as u64;
    for x in &mut h.eps {
        *x = nx2(&mut p, st);
    }
    h.cs = nx(&mut p);
    h.theta0 = nx2(&mut p, st);
    {
        let experts = h.ne > 0;
        for i in [KQ_, KV_, KO_, KGD, KUD, KDD, KR_] {
            h.hf[i] = nx(&mut p);
        }
        h.hf[KK_] = h.hf[KQ_];
        let (gs, us) = if experts { (h.hf[KGD], h.hf[KUD]) } else { (0, 0) };
        h.hf[KGS] = gs;
        h.hf[KGR] = gs;
        h.hf[KUS] = us;
        h.hf[KUR] = us;
        h.hf[KDM] = if experts { h.hf[KDD] } else { 0 };
    }
    h.ut = nx(&mut p);
    h.off_h_calls = p;
    for x in &mut h.h_calls {
        *x = nx(&mut p);
    }
    h.la = nx(&mut p);
    h.nmin = nx(&mut p);
    h.dd = nx(&mut p) as u64;
    h.tau = nx(&mut p);
    h.lmaf = nx(&mut p);
    h.naf = nx(&mut p);
    h.lmad = nx(&mut p);
    h.nad = nx(&mut p);
    h.lmar = nx(&mut p);
    h.lmb = nx(&mut p);
    h.lmq = nx(&mut p);
    h.lmx = nx(&mut p);
    for x in &mut h.wb {
        *x = nx(&mut p);
    }
    for x in &mut h.iota {
        *x = nx(&mut p);
    }
    p += 2; // seed_lo, seed_hi
    h.off_h_ts = p;
    for x in &mut h.h_ts {
        *x = nx(&mut p);
    }
    for x in &mut h.h_sig {
        *x = nx(&mut p);
    }
    for x in &mut h.h_rope {
        *x = nx(&mut p);
    }
    for x in &mut h.h_kv {
        *x = nx(&mut p);
    }
    h.off_a = p;
    h.l_b = nx(&mut p);
    h.sx = nx(&mut p);
    h.rx = nx(&mut p);
    h.kfm = nx(&mut p);
    h.kfd = nx(&mut p);
    h.lms = nx(&mut p);
    h.nas = nx(&mut p);
    h.lmh = nx(&mut p);
    h.lmo = nx(&mut p);
    h.lmba = nx(&mut p);
    h.iotaa0 = nx(&mut p);
    h.off_h_texp = p;
    for x in &mut h.h_texp {
        *x = nx(&mut p);
    }
    h.off_h_calls_a = p;
    for x in &mut h.h_calls_a {
        *x = nx(&mut p);
    }
    h.off_eh = p;
    h.mf = nx(&mut p);
    h.kf = nx(&mut p);
    h.epsf = nx2(&mut p, st);
    h.toksrc = nx(&mut p);
    h.lmhf = nx(&mut p);
    h.nhf = nx(&mut p);
    h.lmhd = nx(&mut p);
    h.lmhr = nx(&mut p);
    h.lmbh = nx(&mut p);
    for x in &mut h.wbh {
        *x = nx(&mut p);
    }
    for x in &mut h.iotah {
        *x = nx(&mut p);
    }
    h.clipc = nx(&mut p);
    h.theta = nx(&mut p);
    h.cap = nx(&mut p);
    h.logs = nx(&mut p);
    h.digsh = nx(&mut p);
    h.tabs = nx(&mut p);
    h.famf = nx(&mut p);
    h.off_h_calls_h = p;
    for x in &mut h.h_calls_h {
        *x = nx(&mut p);
    }
    h.off_h_tok = p;
    for x in &mut h.h_tok {
        *x = nx(&mut p);
    }
    h.ytok = nx(&mut p);
    state.stated_target.at = p;
    state.stated_target.hb = nx(&mut p);
    h.at_w = p;
    p += 4;
    if p != st.len() {
        return Err(Refusal::internal("internal-header-length"));
    }
    Ok(h)
}

/// The results of the strict scan (`struct PolScan`).
pub struct PolScan {
    pub frame: Parameters,
    pub st: Vec<u32>,
    pub so: StOwn,
    pub h: Hdr,
    pub pol_calls: Vec<Vec<String>>,
    pub pol_calls_h: Vec<Vec<String>>,
    pub pol_calls_a: Vec<Vec<String>>,
    pub lidb_seen: bool,
    pub nmin_h_seen: bool,
    pub eg_seen: bool,
    pub smax_seen: bool,
    pub xl_seen: bool,
    pub tbl_pol: [[u32; DW]; 4],
    pub tbl_at: usize,
}

impl Default for PolScan {
    fn default() -> Self {
        Self {
            frame: Parameters::default(),
            st: Vec::new(),
            so: StOwn::default(),
            h: Hdr::default(),
            pol_calls: Vec::new(),
            pol_calls_h: Vec::new(),
            pol_calls_a: Vec::new(),
            lidb_seen: false,
            nmin_h_seen: false,
            eg_seen: false,
            smax_seen: false,
            xl_seen: false,
            tbl_pol: [[0; DW]; 4],
            tbl_at: 0,
        }
    }
}

fn pol_lay_w(ps: &mut PolScan, i: usize, v: u32) -> Result<()> {
    if i >= ps.st.len() || ps.so.laid.len() != ps.st.len() {
        return Err(Refusal::internal("internal-statement-cover"));
    }
    if ps.so.laid[i] && ps.st[i] != v {
        return Err(Refusal::internal("internal-statement-twice"));
    }
    ps.st[i] = v;
    ps.so.laid[i] = true;
    Ok(())
}

/// `layW`: writes word `i` of the statement (`cp_verify.cpp:1308-1310`; the C++ `polLayW`).
pub fn lay_w(ps: &mut PolScan, i: usize, v: u32) -> Result<()> {
    pol_lay_w(ps, i, v)
}

/// `ownW`: writes the digest `w` at statement words `at .. at + w.len()`.
pub fn lay_words(ps: &mut PolScan, at: usize, w: &[u32]) -> Result<()> {
    for (j, &x) in w.iter().enumerate() {
        pol_lay_w(ps, at + j, x)?;
    }
    Ok(())
}

/// `stFromCall` (`cp_verify.cpp:316-325`): fills `so` from the request `p` (T tokens, then r and e)
/// and the one word `q` of y. Only the length, the range and y's range are tested.
pub fn st_from_call(so: &mut StOwn, p: &[u32], q: &[u32], t: u64) -> Result<()> {
    if p.is_empty() || q.is_empty() {
        return Err(Refusal::named("statement-required"));
    }
    if p.len() as u64 != t + 2 || q.len() != 1 {
        return Err(Refusal::named("statement-range"));
    }
    so.req = p.to_vec();
    so.tok = p[..t as usize].to_vec();
    so.r = p[t as usize];
    so.e = p[t as usize + 1];
    so.y = q[0];
    if so.r >= so.e || so.e as u64 > t || (so.e as u64) < t && so.y != 0 {
        return Err(Refusal::named("statement-range"));
    }
    Ok(())
}

/// `polPrescan`: reads version, prof, lt and toksrc.
pub fn pol_prescan(ps: &mut PolScan, pol_b: &[u8], state: &mut StageState) -> Result<()> {
    let fault = match read_parameters(pol_b, &mut ps.frame) {
        Ok(()) => None,
        Err(f) => Some(f),
    };
    if let Some(fault) = fault {
        let a = fault.find(": ").unwrap_or(usize::MAX);
        let b = fault.find(" (line ").unwrap_or(usize::MAX);
        let end = a.min(b);
        let name = &fault[..end];
        if name.starts_with("version-") {
            let _ = admit_word(state, ps.frame.version);
        }
        if name.starts_with("parameter-") {
            return Err(Refusal::internal("internal-parameter-name"));
        }
        return Err(Refusal::named(&format!("{} (policy)", name)));
    }
    ps.so.hv = true;
    ps.so.pv = ps.frame.version as u64;
    ps.so.hp = pol_word(&ps.frame.rest, "prof").map(|v| {
        ps.so.pp = v;
        true
    }).unwrap_or(false);
    ps.so.hl = pol_word(&ps.frame.rest, "lt").map(|v| {
        ps.so.plt = v;
        true
    }).unwrap_or(false);
    ps.so.ht = pol_word(&ps.frame.rest, "toksrc").map(|v| {
        ps.so.pts = v;
        true
    }).unwrap_or(false);
    let _ = admit_word(state, ps.frame.version);
    if !ps.so.hp || (ps.so.pp >> 4) != 1 || !ps.so.ht || ps.so.pts != 1 {
        return Err(Refusal::named("statement-required"));
    }
    Ok(())
}

/// `polSkeleton`: sizes the statement and writes words 0-3, toksrc and (if `with_y`) `so.y`.
pub fn pol_skeleton(ps: &mut PolScan, with_y: bool, state: &mut StageState) -> Result<()> {
    if !admit_word(state, ps.so.pv as u32) {
        return Err(Refusal::named("header-version"));
    }
    ps.st = vec![0u32; statement_length_words()];
    ps.so.laid = vec![false; ps.st.len()];
    pol_lay_w(ps, 0, 0x4D36_3100)?;
    pol_lay_w(ps, 1, ps.so.pv as u32)?;
    pol_lay_w(ps, 2, ps.so.pp as u32)?;
    pol_lay_w(ps, 3, ps.so.plt as u32)?;
    let mut h = parse_header(&ps.st, state)?;
    pol_lay_w(ps, h.off_eh + 4, 1)?;
    if with_y {
        pol_lay_w(ps, h.off_h_tok + DW, ps.so.y)?;
    }
    h = parse_header(&ps.st, state)?;
    ps.h = h;
    Ok(())
}

fn call_line(tokens: &[u8]) -> Result<Vec<String>> {
    // Form of a call line: "call <name> <kind> <SEG> ...".
    if tokens.is_empty() || tokens[tokens.len() - 1] != b'\n' {
        return Err(Refusal::named("policy-call-line"));
    }
    let s = &tokens[..tokens.len() - 1];
    let mut tok: Vec<String> = Vec::new();
    let mut a = 0usize;
    loop {
        let b = s[a..].iter().position(|&c| c == b' ').map(|i| a + i);
        let end = b.unwrap_or(s.len());
        let t = &s[a..end];
        if t.is_empty() {
            return Err(Refusal::named("policy-call-line"));
        }
        for &ch in t {
            if !(ch.is_ascii_alphanumeric() || ch == b'.' || ch == b'_' || ch == b'-') {
                return Err(Refusal::named("policy-call-line"));
            }
        }
        tok.push(core::str::from_utf8(t).unwrap().to_string());
        match b {
            Some(b) => a = b + 1,
            None => break,
        }
    }
    if tok.len() > 1 && tok[1].len() > 8 {
        return Err(Refusal::named("policy-call-line"));
    }
    Ok(tok)
}

/// `polScan`: the strict scan of the lines after the leading ones.
pub fn pol_scan(ps: &mut PolScan, pol_b: &[u8], state: &mut StageState) -> Result<()> {
    let mut nm: Vec<String> = vec![
        "magic".into(), "version".into(), "prof".into(), "lt".into(), "L".into(), "ll".into(), "d".into(),
        "H".into(), "G".into(), "dh".into(), "f".into(), "fe".into(), "NE".into(), "V".into(), "eps1_lo".into(),
        "eps1_hi".into(), "eps2_lo".into(), "eps2_hi".into(), "cs".into(), "theta0_lo".into(), "theta0_hi".into(),
    ];
    for s in ["hq", "hv", "ho", "hgD", "huD", "hdD", "hr", "ut"] {
        nm.push(s.into());
    }
    let gap_at = nm.len();
    for s in [
        "la", "nmin", "D", "tau", "lmaf", "NAf", "lmad", "NAd", "lmar", "lmb", "lmq", "lmx",
    ] {
        nm.push(s.into());
    }
    for k in ["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"] {
        nm.push(format!("wb_{}", k));
    }
    for c in 0..8 {
        nm.push(format!("iota_{}", c));
    }
    for s in ["seed_lo", "seed_hi"] {
        nm.push(s.into());
    }
    let n_base = nm.len();
    for s in ["lB", "S", "rx", "kFM", "kFD", "lmS", "NAs", "lmh", "lmo", "lmbA", "iotaA_0"] {
        nm.push(s.into());
    }
    let n_a = nm.len();
    for s in [
        "MF", "KF", "epsF_lo", "epsF_hi", "toksrc", "lmhf", "NHf", "lmhd", "lmhr", "lmbH", "wb_emb", "wb_head",
        "iotaH_0", "iotaH_1", "iotaH_2", "iotaH_3", "iotaH_4", "iotaH_5", "C", "theta", "cap", "s", "sh", "sT", "F",
    ] {
        nm.push(s.into());
    }
    let n_e = nm.len();
    let tblw = 4 * DW;
    let mut i = 2usize;
    let mut tbl_prev = false;
    let mut ll_seen = false;
    let rest = ps.frame.rest.clone();
    let mut it = LineIter::new(&rest);
    loop {
        let line = match it.next_line(1024) {
            Ok(None) => break,
            Ok(Some(l)) => l,
            Err(2) => return Err(Refusal::named("policy-line-long")),
            Err(_) => return Err(Refusal::named("policy-zero-byte")),
        };
        let after_tbl = tbl_prev;
        tbl_prev = false;
        if i < nm.len() {
            if digits_beyond_scan(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            let (name, val) = scanned(line).ok_or_else(|| Refusal::named(&format!("policy-line-{}", i)))?;
            if val > 0xFFFF_FFFF {
                return Err(Refusal::named(&format!("policy-line-{}", i)));
            }
            if nm[i] != name {
                return Err(Refusal::named(&format!("policy-name-{}", nm[i])));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            let at = if i < n_base {
                i + if i >= gap_at { DW } else { 0 }
            } else if i < n_a {
                ps.h.off_a + (i - n_base)
            } else {
                ps.h.off_eh + (i - n_a)
            };
            pol_lay_w(ps, at, val as u32)?;
            i += 1;
            if i == n_e {
                // `frameWords`: the words of block HD and W, from the leading lines.
                if ps.frame.table_data >> 32 != 0 || ps.frame.table_random >> 32 != 0 {
                    return Err(Refusal::named("parameter-table-shape (policy)"));
                }
                for kind in &ps.frame.work {
                    for &bits in kind {
                        if bits > WORK_BITS_MOST {
                            return Err(Refusal::named("policy-work-most"));
                        }
                    }
                }
                let depth = ceil_log2(ps.frame.slots);
                if depth > 8 {
                    return Err(Refusal::named("policy-leafd"));
                }
                let sec = ps.frame.sec;
                let at_w = ps.h.at_w;
                let block_log = ps.frame.block_log;
                let table_rows_log = ps.frame.table_rows_log;
                let table_log_n = ps.frame.table_log_n;
                let table_random = ps.frame.table_random as u32;
                pol_lay_w(ps, state.stated_target.at, sec)?;
                pol_lay_w(ps, at_w, block_log)?;
                pol_lay_w(ps, at_w + 1, table_rows_log)?;
                pol_lay_w(ps, at_w + 2, table_log_n)?;
                pol_lay_w(ps, at_w + 3, table_random)?;
                state.pow = ps.frame.work[3][0] as i32;
                state.pows = ps.frame.work[3][1] as i32;
                state.powc = ps.frame.work[3][2] as i32;
                i = nm.len();
                ll_seen = true;
            }
            continue;
        }
        // Not lines of the format.
        if line.starts_with(b"clt ") || line.starts_with(b"clns ") || line.starts_with(b"cms ") {
            return Err(Refusal::named("policy-cert-words"));
        }
        let scan = scanned(line);
        if line.starts_with(b"lidb ") {
            if !ll_seen
                || ps.lidb_seen
                || ps.nmin_h_seen
                || ps.eg_seen
                || ps.smax_seen
                || state.rcl != 0
                || state.gcl != 0
                || ps.xl_seen
                || ps.tbl_at != 0
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
            {
                return Err(Refusal::named("policy-lidb"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            let val = scan.unwrap().1;
            if val <= LIDB_SEALED as u64 {
                return Err(Refusal::named("policy-lidb"));
            }
            if val > LIDB_MAX as u64 {
                return Err(Refusal::named("plan-identity-cap"));
            }
            state.lidb = val as i32;
            ps.lidb_seen = true;
            continue;
        }
        if line.starts_with(b"nminH ") {
            if !ll_seen
                || !ps.lidb_seen
                || ps.nmin_h_seen
                || ps.eg_seen
                || ps.smax_seen
                || state.rcl != 0
                || state.gcl != 0
                || ps.xl_seen
                || ps.tbl_at != 0
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
            {
                return Err(Refusal::named("policy-nminH"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            let val = scan.unwrap().1;
            if val < 2 || val > NMINH_MAX as u64 {
                return Err(Refusal::named("policy-nminH"));
            }
            state.nminh = val as i32;
            ps.nmin_h_seen = true;
            continue;
        }
        if line.starts_with(b"eg ") || line.starts_with(b"smax ") {
            let is_eg = line[0] == b'e';
            if !ll_seen
                || ps.smax_seen
                || (is_eg && ps.eg_seen)
                || state.rcl != 0
                || state.gcl != 0
                || ps.xl_seen
                || ps.tbl_at != 0
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
            {
                return Err(Refusal::named("policy-gate-table"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            let val = scan.unwrap().1;
            if is_eg {
                if !(4..=7).contains(&val) {
                    return Err(Refusal::named("policy-gate-table"));
                }
                state.gate_table_input_fraction_bits = val as i32;
                ps.eg_seen = true;
            } else {
                if !matches!(val, 2047 | 1023 | 511 | 255) {
                    return Err(Refusal::named("policy-gate-table"));
                }
                state.smax = val as i32;
                ps.smax_seen = true;
            }
            continue;
        }
        if line.starts_with(b"rcl ") {
            if !ll_seen
                || state.rcl != 0
                || state.gcl != 0
                || ps.xl_seen
                || ps.tbl_at != 0
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
                || scan.as_ref().unwrap().1 != 1
            {
                return Err(Refusal::named("policy-rcl"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            state.rcl = 1;
            continue;
        }
        if line.starts_with(b"gcl ") {
            if !ll_seen
                || state.gcl != 0
                || ps.xl_seen
                || ps.tbl_at != 0
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
                || scan.as_ref().unwrap().1 != 1
            {
                return Err(Refusal::named("policy-gcl"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            state.gcl = 1;
            continue;
        }
        if line.starts_with(b"xl ") {
            if !ll_seen
                || ps.xl_seen
                || ps.tbl_at != 0
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
            {
                return Err(Refusal::named("policy-xl"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            if scan.unwrap().1 != 5 {
                return Err(Refusal::named("policy-xl"));
            }
            state.residual_stream_limbs = 5;
            ps.xl_seen = true;
            continue;
        }
        if line.starts_with(b"tsilu") || line.starts_with(b"tsig") || line.starts_with(b"trope") || line.starts_with(b"texp") {
            const TB: [&str; 4] = ["tsilu", "tsig", "trope", "texp"];
            if !ll_seen
                || ps.tbl_at >= tblw
                || (ps.tbl_at != 0 && !after_tbl)
                || !ps.pol_calls.is_empty()
                || !ps.pol_calls_a.is_empty()
                || !ps.pol_calls_h.is_empty()
                || scan.is_none()
                || scan.as_ref().unwrap().1 > 0xFFFF_FFFF
            {
                return Err(Refusal::named("policy-tables"));
            }
            if !word_line_form(line) {
                return Err(Refusal::named("policy-line-form"));
            }
            let (name, val) = scan.unwrap();
            if format!("{}{}", TB[ps.tbl_at / DW], ps.tbl_at % DW) != name {
                return Err(Refusal::named("policy-tables"));
            }
            ps.tbl_pol[ps.tbl_at / DW][ps.tbl_at % DW] = val as u32;
            ps.tbl_at += 1;
            tbl_prev = true;
            continue;
        }
        let tok = call_line(line)?;
        let kind_l = match tok[0].as_str() {
            "call" => 0,
            "callA" => 1,
            "callH" => 2,
            _ => -1,
        };
        if tok.len() < 4
            || kind_l < 0
            || (kind_l == 0 && (!ps.pol_calls_a.is_empty() || !ps.pol_calls_h.is_empty()))
            || (kind_l == 1 && !ps.pol_calls_h.is_empty())
        {
            return Err(Refusal::named("policy-call-line"));
        }
        let v: Vec<String> = tok[1..].to_vec();
        match kind_l {
            0 => ps.pol_calls.push(v),
            1 => ps.pol_calls_a.push(v),
            _ => ps.pol_calls_h.push(v),
        }
    }
    if i != nm.len() {
        return Err(Refusal::named("policy-length"));
    }
    if ps.tbl_at != 0 && ps.tbl_at != tblw {
        return Err(Refusal::named("policy-tables"));
    }
    let _ = pol_b;
    Ok(())
}

/// A tensor: a named family of values in a committed matrix (`struct Ten`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ten {
    pub name: String,
    pub mat: i32,
    pub nl: i32,
    pub cnt: u64,
    pub j: u64,
    pub off: u64,
}

impl Ten {
    pub fn at(&self) -> TenAt {
        TenAt { off: self.off, nl: self.nl as u64, cnt: self.cnt, j: self.j }
    }
}

/// A lookup segment (`struct Seg`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Seg {
    pub name: String,
    pub n: u64,
    pub pos: Vec<u64>,
    pub moe: bool,
}

/// A lookup call (`struct CallD`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallD {
    pub c: super::common::Call,
    pub kind: String,
    pub segs: Vec<Seg>,
    pub j: u64,
    pub l_j: i32,
    pub used: Vec<u8>,
}

impl CallD {
    /// `CallD::padding(lam, j)`.
    pub fn padding(&self, lam: u64, j: usize) -> bool {
        self.used[j] == 0 || (self.used[j] == 2 && lam % 2 == 0)
    }
    /// `CallD::seg(name)`.
    pub fn seg(&self, n: &str) -> Result<&Seg> {
        self.segs.iter().find(|s| s.name == n).ok_or_else(|| Refusal::internal(&format!("internal-segment-{}", n)))
    }
}

/// A weight kind (`struct KindD`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KindD {
    pub idx: i32,
    pub name: String,
    pub l: u64,
    pub segs: u64,
}

/// The layout of a layer sub-proof (`struct Lay`).
#[derive(Clone, Debug, Default)]
pub struct Lay {
    pub h: Hdr,
    pub t: u64,
    pub lam: u64,
    pub ngr: u64,
    pub pd: u64,
    pub pf: u64,
    pub s2: u64,
    pub nw: u64,
    pub nn: u64,
    pub ni: u64,
    pub dq: u64,
    pub dkv: u64,
    pub nqk: u64,
    pub l_pf: i32,
    pub lfe: i32,
    pub l_pd: i32,
    pub ls: i32,
    pub ldh: i32,
    pub ten: Vec<Ten>,
    pub feat: [u64; 4],
    pub filled: [u64; 4],
    pub kcol: [u64; 4],
    pub mrow: [u64; 4],
    pub parts: [u64; 4],
    pub xb_filled: u64,
    pub kxb: u64,
    pub mxb: u64,
    pub xb: TenAt,
    pub kinds: Vec<KindD>,
    pub calls: Vec<CallD>,
    pub tau_fc: Vec<u64>,
    pub tau_fl: Vec<u64>,
    pub tau_fs: Vec<u64>,
    pub lam_m: u64,
    pub l_ne: i32,
    pub kbm: u64,
    pub fo: HForest,
}

impl Lay {
    /// `Lay::T_(name)`.
    pub fn t_(&self, n: &str) -> Result<&Ten> {
        self.ten.iter().find(|t| t.name == n).ok_or_else(|| Refusal::internal(&format!("internal-tensor-{}", n)))
    }
}

/// `groupsBaseHeld`.
pub fn groups_base_held(ngr: u64) -> Result<()> {
    if 2 + 2 * ngr > 59 {
        return Err(Refusal::named("plan-groups-base"));
    }
    Ok(())
}

/// `tensorsAgree`.
pub fn tensors_agree(owner: &[(String, TenAt)], reader: &[(String, TenAt)]) -> Result<()> {
    if owner.len() != reader.len() {
        return Err(Refusal::named("plan-tensor-layout"));
    }
    for i in 0..owner.len() {
        let (o, r) = (&owner[i].1, &reader[i].1);
        if owner[i].0 != reader[i].0
            || o.off != r.off
            || o.nl != r.nl
            || o.cnt != r.cnt
            || o.j != r.j
        {
            return Err(Refusal::named("plan-tensor-layout"));
        }
    }
    Ok(())
}

/// `tensorsFill`.
pub fn tensors_fill(ten: &[(String, TenAt)], feat: u64, s2: u64, arr: &str) -> Result<()> {
    let name = format!("plan-tensor-layout-fill-{}", arr);
    let mut run: Vec<(u64, u64)> = Vec::new();
    for (_, x) in ten {
        if x.j == 0 || x.j % s2 != 0 {
            return Err(Refusal::named(&name));
        }
        for l in 0..x.nl {
            for i in 0..x.cnt {
                run.push((ten_cell(x, l, i, 0), x.j));
            }
        }
    }
    run.sort();
    let mut at = 0u64;
    for (first, len) in run {
        if first != at {
            return Err(Refusal::named(&name));
        }
        at += len;
    }
    if at != feat {
        return Err(Refusal::named(&name));
    }
    Ok(())
}

/// `place`: places a call's segments in `2^lJ` aligned columns.
pub fn place(cd: &mut CallD, floor_lg: i32) {
    struct Pc {
        s: usize,
        first: u64,
        size: u64,
    }
    let mut pcs: Vec<Pc> = Vec::new();
    for s in 0..cd.segs.len() {
        let mut first = 0u64;
        for b in (0..=40).rev() {
            if (cd.segs[s].n >> b) & 1 != 0 {
                pcs.push(Pc { s, first, size: 1u64 << b });
                first += 1u64 << b;
            }
        }
        cd.segs[s].pos = vec![0; cd.segs[s].n as usize];
    }
    pcs.sort_by(|a, b| b.size.cmp(&a.size));
    let mut off = 0u64;
    for p in &pcs {
        for x in 0..p.size {
            cd.segs[p.s].pos[(p.first + x) as usize] = off + x;
        }
        off += p.size;
    }
    cd.l_j = ceil_log2(off) as i32;
    if cd.l_j < floor_lg {
        cd.l_j = floor_lg;
    }
    cd.j = 1u64 << cd.l_j;
    cd.used = vec![0u8; cd.j as usize];
    for s in &cd.segs {
        for &p in &s.pos {
            cd.used[p as usize] = if s.moe { 2 } else { 1 };
        }
    }
}

/// `layout`: tests the statement's parameters and derives the layout.
pub fn layout(h: &Hdr, pc: &[Vec<String>], state: &StageState) -> Result<Lay> {
    let mut y = Lay::default();
    y.h = h.clone();
    let d = h.d;
    let f = h.f;
    let fe = h.fe;
    if h.prof != 4 {
        return Err(Refusal::named("policy-profile"));
    }
    let p3 = h.ne > 0;
    y.nw = 2;
    y.nn = 2;
    if h.lt < 4
        || h.lt > 16
        || h.ll < 1
        || h.ll > 6
        || d == 0
        || f == 0
        || d > (1u64 << 20)
        || f > (1u64 << 20)
        || (p3 && ((fe & (fe - 1)) != 0 || f != 2 * fe || (h.ll == 1 && fe == 1)))
    {
        return Err(Refusal::named("shape-words"));
    }
    y.t = 1u64 << h.lt;
    y.lam = 1u64 << h.ll;
    if h.l == 0 || h.l as u64 % y.lam != 0 {
        return Err(Refusal::named("shape-L"));
    }
    y.ngr = h.l as u64 / y.lam;
    if 2 + 2 * y.ngr >= (1u64 << 16) {
        return Err(Refusal::named("shape-groups"));
    }
    groups_base_held(y.ngr)?;
    y.pd = 1u64 << ceil_log2(d);
    y.l_pd = ceil_log2(y.pd) as i32;
    y.pf = 1u64 << ceil_log2(f);
    y.l_pf = ceil_log2(y.pf) as i32;
    if p3 {
        y.lfe = ceil_log2(fe) as i32;
    }
    if h.la <= h.lt || h.la > 16 {
        return Err(Refusal::named("shape-la"));
    }
    y.ls = (h.la - h.lt) as i32;
    y.s2 = 1u64 << y.ls;
    if d % y.s2 != 0 || f % y.s2 != 0 || (p3 && fe % y.s2 != 0) {
        return Err(Refusal::named("shape-la"));
    }
    for n in 0..2 {
        if h.eps[n] < 1 || h.eps[n] >= (1u64 << 59) {
            return Err(Refusal::named("policy-norm"));
        }
    }
    if h.h == 0
        || h.gk == 0
        || h.dh == 0
        || (h.dh & (h.dh - 1)) != 0
        || h.dh < 2
        || h.h * h.dh != d
        || h.h + h.gk > 64
    {
        return Err(Refusal::named("shape-heads"));
    }
    y.dq = h.h * h.dh;
    y.dkv = h.gk * h.dh;
    y.nqk = y.dq + y.dkv;
    y.ldh = ceil_log2(h.dh) as i32;
    if y.dkv % y.s2 != 0 || y.nqk % y.s2 != 0 {
        return Err(Refusal::named("shape-la"));
    }
    if h.cs != 12 {
        return Err(Refusal::named("policy-cs"));
    }
    {
        let mut present = vec![KGD, KUD, KDD, KQ_, KK_, KV_, KO_];
        if p3 {
            for i in [KR_, KGS, KUS, KGR, KUR, KDM] {
                present.push(i);
            }
        }
        for i in 0..13 {
            let pr = present.contains(&i);
            if !pr {
                if h.hf[i] != 0 {
                    return Err(Refusal::named("header-absent-class"));
                }
                continue;
            }
            if h.hf[i] > 2 {
                return Err(Refusal::named("policy-forms"));
            }
        }
        if h.ut != 1 {
            return Err(Refusal::named("policy-ut"));
        }
    }
    if h.dd < 2 || h.dd > 4096 || (h.dd & (h.dd - 1)) != 0 {
        return Err(Refusal::named("shape-D"));
    }
    let lam = y.lam;
    y.ni = y.nn * lam;
    let mut off = [0u64; 4];
    let ne = h.ne;
    let lam_m = lam / 2;
    y.lam_m = lam_m;
    if p3 {
        if ne < 2 || ne > 4096 || (ne & (ne - 1)) != 0 {
            return Err(Refusal::named("shape-NE"));
        }
        y.l_ne = ceil_log2(ne) as i32;
    }
    let gcl = state.gcl != 0;
    let rcl = state.rcl != 0;
    let limbs = state.residual_stream_limbs;
    let mut add = |name: &str, mat: usize, nl: i32, cnt: u64, j: u64| {
        if nl == 0 {
            return;
        }
        y.ten.push(Ten {
            name: name.to_string(),
            mat: mat as i32,
            nl,
            cnt,
            j,
            off: off[mat],
        });
        off[mat] += nl as u64 * cnt * j;
    };
    if gcl && !p3 {
        return Err(Refusal::named("policy-gcl"));
    }
    if gcl {
        add("g0", 0, 1, lam, f);
        add("gc", 0, 1, lam, f);
    } else {
        add("gi", 0, 2, lam, f);
    }
    add("s", 0, 2, lam, f);
    add("u", 0, 2, lam, f);
    add("rg", 0, h.hf[KGD] as i32, lam, f);
    add("ru", 0, h.hf[KUD] as i32, lam, f);
    add("xs", 0, limbs, y.nw * lam - 1, d);
    add("ro", 0, h.hf[KO_] as i32, lam, d);
    add("rd", 0, h.hf[KDD] as i32, lam, d);
    add("aw", 0, 2, lam, d);
    add("ra", 0, 2, lam, d);
    add("mw", 0, 2, lam, d);
    add("rm", 0, 2, lam, d);
    add("qkw", 0, 2, lam, y.nqk);
    add("rqk", 0, h.hf[KQ_] as i32, lam, y.nqk);
    add("vw", 0, 2, lam, y.dkv);
    add("rv", 0, h.hf[KV_] as i32, lam, y.dkv);
    if gcl {
        add("gh", 0, 2, lam, f);
    }
    add("a", 1, 2, lam, d);
    add("m", 1, 2, lam, d);
    if p3 {
        add("xr", 1, 2, lam_m, d);
        add("lr", 2, 2, lam_m, ne);
        add("rl", 2, h.hf[KR_] as i32, lam_m, ne);
        add("sel", 2, 1, lam_m, ne);
        add("sc", 2, 3, lam_m, 1);
    }
    add("row", 2, 1, y.nn * lam, led_nr_local(limbs));
    if rcl && !p3 {
        return Err(Refusal::named("policy-rcl"));
    }
    if rcl {
        add("ly", 2, 2, lam_m, ne);
        add("l3", 2, 1, lam_m, ne);
    }
    add("q", 3, 2, lam, y.dq);
    add("kx", 3, 2, lam, y.dkv);
    add("v", 3, 2, lam, y.dkv);
    add("o", 3, 2, lam, y.dq);
    let lm = [h.lmaf, h.lmad, h.lmar, h.lmq];
    let na = [h.naf, h.nad, 1u32, 1u32];
    if h.lmq < h.la {
        return Err(Refusal::named("shape-la"));
    }
    for m in 0..4 {
        if lm[m] < h.lt || lm[m] > 24 || na[m] == 0 || na[m] > 64 {
            return Err(Refusal::named("shape-request-matrix"));
        }
        y.feat[m] = off[m];
        y.mrow[m] = 1u64 << lm[m];
        y.parts[m] = na[m] as u64;
        let unit = na[m] as u64 * (y.mrow[m] / y.t);
        y.filled[m] = (off[m] + unit - 1) / unit * unit;
        y.kcol[m] = y.filled[m] / unit;
    }
    if h.lmaf < h.la {
        return Err(Refusal::named("shape-la"));
    }
    if h.lmx < h.la || h.lmx > 24 {
        return Err(Refusal::named("shape-request-matrix"));
    }
    y.mxb = 1u64 << h.lmx;
    {
        let unit = y.mxb / y.t;
        let nlx = limbs as u64;
        y.xb_filled = (nlx * d + unit - 1) / unit * unit;
        y.kxb = y.xb_filled / unit;
        y.xb = TenAt { off: 0, nl: nlx, cnt: 1, j: d };
        tensors_fill(&[("x".to_string(), y.xb)], nlx * d, y.s2, "stream")?;
        let qa: Vec<(String, TenAt)> = y
            .ten
            .iter()
            .filter(|t| t.mat == 3)
            .map(|t| (t.name.clone(), t.at()))
            .collect();
        tensors_fill(&qa, y.feat[3], y.s2, "qa")?;
    }
    y.tau_fc = vec![0; 65536];
    y.tau_fl = vec![0; 65536];
    let tp = TableParams {
        eg: state.gate_table_input_fraction_bits as u32,
        smax: state.smax,
        gcl,
        ..TableParams::default()
    };
    for t in 0..65536usize {
        let c = (t as i64 - 32768).clamp(-(super::attention_shape::CLAMP as i64), super::attention_shape::CLAMP as i64);
        y.tau_fc[t] = t as u64 + (((c + super::attention_shape::CLAMP as i64 + 1) as u64) << 28);
        y.tau_fl[t] = t as u64
            + (((gate_table_entry(&tp, t as i32) + 4096) as u64) << 28);
    }
    if p3 {
        y.tau_fs = vec![0; 65536];
        for t in 0..65536usize {
            let e = sigmoid_clamp_table_entry(&tp, t as i32);
            y.tau_fs[t] = if gcl && t >= 32768 {
                t as u64 + ((e as u64) << 28) + (1u64 << 40)
            } else {
                t as u64 + ((e as u64) << 17)
            };
        }
    }
    // Lookup segments present, and the parameter file's call lines.
    #[derive(Clone)]
    struct Sd {
        name: &'static str,
        kind: &'static str,
        n: u64,
        moe: bool,
    }
    let mut sd: Vec<Sd> = Vec::new();
    fn push_sd(sd: &mut Vec<Sd>, n: &'static str, k: &'static str, len: u64, moe: bool) {
        sd.push(Sd { name: n, kind: k, n: len, moe });
    }
    fn hi_sd(sd: &mut Vec<Sd>, n: &'static str, form: u32, len: u64, moe: bool) {
        if form != 0 {
            sd.push(Sd { name: n, kind: if form == 1 { "R8" } else { "R16" }, n: len, moe });
        }
    }
    push_sd(&mut sd, "G", "R16", f, false);
    push_sd(&mut sd, "U", "R16", f, false);
    push_sd(&mut sd, "UT", "R16", f, false);
    push_sd(&mut sd, "QK", "R16", y.nqk, false);
    hi_sd(&mut sd, "QKH", h.hf[KQ_], y.nqk, false);
    push_sd(&mut sd, "N1", "R16", d, false);
    push_sd(&mut sd, "N1H", "R16", d, false);
    push_sd(&mut sd, "N2", "R16", d, false);
    push_sd(&mut sd, "N2H", "R16", d, false);
    push_sd(&mut sd, "O", "R16", d, false);
    push_sd(&mut sd, "D", "R16", d, false);
    push_sd(&mut sd, "V", "R16", y.dkv, false);
    if p3 {
        push_sd(&mut sd, "XR", "R16", d, true);
        push_sd(&mut sd, "LR", "R16", ne, true);
        push_sd(&mut sd, "LT", "R16", ne, true);
        push_sd(&mut sd, "DD", "R16", ne, true);
    }
    hi_sd(&mut sd, "GH", h.hf[KGD], f, false);
    hi_sd(&mut sd, "UH", h.hf[KUD], f, false);
    hi_sd(&mut sd, "OH", h.hf[KO_], d, false);
    hi_sd(&mut sd, "DH", h.hf[KDD], d, false);
    hi_sd(&mut sd, "VH", h.hf[KV_], y.dkv, false);
    push_sd(&mut sd, "ROW", "R8", led_nr_local(limbs) * y.nn, false);
    if p3 {
        hi_sd(&mut sd, "LH", h.hf[KR_], ne, true);
        push_sd(&mut sd, "SEL", "R8", ne, true);
        if rcl {
            push_sd(&mut sd, "L3", "R8", ne, true);
        }
    }
    if gcl {
        push_sd(&mut sd, "G0", "R8", f, false);
    }
    push_sd(&mut sd, "CN1", "FC", d, false);
    push_sd(&mut sd, "CN2", "FC", d, false);
    push_sd(&mut sd, "CQK", "FC", y.nqk, false);
    push_sd(&mut sd, "CV", "FC", y.dkv, false);
    if rcl {
        push_sd(&mut sd, "CLR", "FC", ne, true);
    }
    if p3 {
        push_sd(&mut sd, "MR", "FS", 1, true);
    }
    if gcl {
        push_sd(&mut sd, "CG", "FS", f, false);
    }
    push_sd(&mut sd, "F", "FL", f, false);
    // The call list: the parameter file's, or the built-in list.
    let mut cl: Vec<Vec<String>> = pc.to_vec();
    if cl.is_empty() {
        let mk = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        cl = if !p3 {
            vec![
                mk(&["R16a", "R16", "G", "U"]),
                mk(&["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"]),
                mk(&["R16c", "R16", "QK", "QKH"]),
                mk(&["R8a", "R8", "GH", "UH"]),
                mk(&["R8b", "R8", "OH", "DH", "VH", "ROW"]),
                mk(&["FC", "FC", "CN1", "CN2", "CQK", "CV"]),
                mk(&["FL", "FL", "F"]),
            ]
        } else {
            vec![
                mk(&["R16a", "R16", "G", "U"]),
                mk(&["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"]),
                mk(&["R16c", "R16", "QK", "QKH", "XR", "LR", "LT", "DD"]),
                mk(&["R8", "R8", "GH", "UH", "OH", "DH", "VH", "ROW", "LH", "SEL"]),
                mk(&["FC", "FC", "CN1", "CN2", "CQK", "CV"]),
                mk(&["FS", "FS", "MR"]),
                mk(&["FL", "FL", "F"]),
            ]
        };
    }
    if cl.len() > 8 {
        return Err(Refusal::named("policy-call-list"));
    }
    let mut seen = vec![false; sd.len()];
    for ln in &cl {
        if ln.len() < 3 {
            return Err(Refusal::named("policy-call-list"));
        }
        let mut cd = CallD::default();
        cd.c.name = ln[0].clone();
        cd.kind = ln[1].clone();
        if y.calls.iter().any(|o| o.c.name == ln[0]) {
            return Err(Refusal::named("policy-call-list"));
        }
        for own in ["V", "a", "b", "E"] {
            if ln[0] == own {
                return Err(Refusal::named("policy-call-list"));
            }
        }
        for name in &ln[2..] {
            let mut j = 0usize;
            while j < sd.len() && sd[j].name != name {
                j += 1;
            }
            if j == sd.len() || seen[j] || sd[j].kind != ln[1] {
                return Err(Refusal::named("policy-call-list"));
            }
            seen[j] = true;
            cd.segs.push(Seg {
                name: sd[j].name.to_string(),
                n: sd[j].n,
                pos: Vec::new(),
                moe: sd[j].moe,
            });
        }
        y.calls.push(cd);
    }
    if seen.iter().any(|&s| !s) {
        return Err(Refusal::named("policy-call-list"));
    }
    y.kinds.push(KindD { idx: 0, name: "qk".into(), l: 64, segs: 2 * lam * d * h.dh });
    y.kinds.push(KindD { idx: 1, name: "v".into(), l: y.dkv, segs: 2 * lam * d });
    y.kinds.push(KindD { idx: 2, name: "o".into(), l: d, segs: 2 * lam * y.dq });
    {
        let nd = if p3 { lam_m } else { lam };
        y.kinds.push(KindD { idx: 3, name: "g".into(), l: f, segs: 2 * nd * d });
        y.kinds.push(KindD { idx: 4, name: "u".into(), l: f, segs: 2 * nd * d });
    }
    if p3 {
        y.kinds.push(KindD { idx: 5, name: "gs".into(), l: fe, segs: 2 * lam_m * d });
        y.kinds.push(KindD { idx: 6, name: "us".into(), l: fe, segs: 2 * lam_m * d });
        y.kinds.push(KindD { idx: 7, name: "gr".into(), l: fe, segs: 2 * lam_m * ne * d });
        y.kinds.push(KindD { idx: 8, name: "ur".into(), l: fe, segs: 2 * lam_m * ne * d });
    }
    y.kinds.push(KindD {
        idx: 9,
        name: "dn".into(),
        l: d,
        segs: if p3 { 2 * (lam_m * f + lam_m * fe) } else { 2 * lam * f },
    });
    if p3 {
        y.kinds.push(KindD { idx: 10, name: "dnr".into(), l: d, segs: 2 * lam_m * ne * fe });
        y.kinds.push(KindD { idx: 11, name: "r".into(), l: ne, segs: 2 * lam_m * d });
    }
    if h.lmb > 24 {
        return Err(Refusal::named("shape-lmb"));
    }
    if h.nmin > 28 {
        return Err(Refusal::named("shape-words"));
    }
    for q in 0..y.calls.len() {
        let mut cd = y.calls[q].clone();
        let fl = h.nmin as i32 - h.ll as i32 - h.lt as i32;
        place(&mut cd, fl.max(0));
        cd.c.n = (h.ll + cd.l_j as u32 + h.lt) as i32;
        cd.c.iota = h.iota[q] as i32;
        cd.c.kappa = 5;
        cd.c.k = if cd.kind == "R8" { 8 } else { 16 };
        if cd.kind == "FC" || cd.kind == "FL" || cd.kind == "FS" {
            cd.c.func = 1;
            cd.c.t0 = 32768;
        }
        if cd.c.iota < 0 {
            return Err(Refusal::named(&format!("shape-call-{}", cd.c.name)));
        }
        if cd.c.n < 10 || cd.c.n < h.nmin as i32 || cd.c.n > 44 || cd.c.kappa != 5 {
            return Err(Refusal::named(&format!("shape-call-{}", cd.c.name)));
        }
        if cd.c.n < h.la as i32 || cd.l_j < y.ls {
            return Err(Refusal::named(&format!("shape-call-{}", cd.c.name)));
        }
        y.calls[q] = cd;
    }
    {
        let calls: Vec<super::common::Call> = y.calls.iter().map(|c| c.c.clone()).collect();
        let mut fo = forest_shape(&calls, state.lidb)?;
        if fo.d_t < h.la as i32 {
            return Err(Refusal::named("forest-depth-G"));
        }
        y.kbm = forest_plane_cols(&fo, h.lmb as i32)?;
        for q in 0..y.calls.len() {
            if y.calls[q].c.iota != fo.iota[q] {
                return Err(Refusal::named(&format!("shape-call-{}", y.calls[q].c.name)));
            }
        }
        fo.pub_ = vec![0; fo.nt as usize];
        for q in 0..y.calls.len() {
            let cd = &y.calls[q];
            for lam in 0..lam {
                for j in 0..cd.j {
                    if cd.padding(lam, j as usize) {
                        let b = (lam * cd.j + j) >> (fo.d_t as u64 - h.lt as u64);
                        if b >> fo.iota[q] != 0 {
                            return Err(Refusal::internal("internal-forest-pub"));
                        }
                        fo.pub_[(fo.first[q] as u64 + b) as usize] += y.t;
                    }
                }
            }
        }
        let names = fo.names.clone();
        let pub_ = fo.pub_.clone();
        forest_pub_ask(&fo, &names, &pub_, "")?;
        y.fo = fo;
    }
    for q in y.calls.len()..8 {
        if h.iota[q] != 0 {
            return Err(Refusal::named("header-absent-call"));
        }
    }
    if y.nw != 2 || y.nn != y.nw || y.ni != y.nn * y.lam {
        return Err(Refusal::internal("internal-layout-words"));
    }
    Ok(y)
}

/// `ledNR` from the stage's limb count (the C++ global `residualStreamLimbs`).
fn led_nr_local(limbs: i32) -> u64 {
    super::norm_digit_rows::led_nr(limbs) as u64
}

/// `setTau`: points each call at the layout's table vectors.
pub fn set_tau(dst: &mut Lay, src: &Lay) {
    for c in &mut dst.calls {
        c.c.tau = match c.kind.as_str() {
            "FC" => Some(src.tau_fc.clone()),
            "FL" => Some(src.tau_fl.clone()),
            "FS" => Some(src.tau_fs.clone()),
            _ => None,
        };
    }
}
