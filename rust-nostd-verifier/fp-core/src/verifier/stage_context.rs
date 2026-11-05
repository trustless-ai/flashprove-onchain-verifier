//! The context that the layer and output-head sub-proofs use, ported from the rest of
//! `verifier/src/cp_verify.cpp`'s `runStage`: the per-layer RoPE bits from KL.bin, the layers'
//! range-check matrices (`tails`), the weight layout (`wsLay`), and the output head's layout
//! (`HLy`: its own matrices, calls and lookup forest).

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use crate::numbers::codes::ceil_log2;
use crate::refusal::{Refusal, Result};
use crate::stage_state::StageState;

use super::attention_shape::CLAMP;
use super::lookup::{forest_plane_cols, forest_pub_ask, forest_shape, HForest};
use super::matrices::{TMat, Tail};
use super::norm_digit_rows::{led_nrh, BIGH, EXC};
use super::packing::KCAP;
use super::stage_layout::{place, CallD, Hdr, Lay, Seg};
use super::weights_layout::{ws_set_moe, WsLay, WsShape};

/// The number of bits of a weight of any kind except the embedding.
pub const WEIGHT_WIDTH_BITS: u32 = 13;
/// `WEIGHT_BOUND`.
pub const WEIGHT_BOUND: u32 = 1 << (WEIGHT_WIDTH_BITS - 1);

/// Words per layer record in KL.bin.
pub const KW_: usize = 13;
/// The word indices of a layer record.
pub const LKQ: usize = 0;
pub const LKK: usize = 1;
pub const LKV: usize = 2;
pub const LKO: usize = 3;
pub const LKG: usize = 4;
pub const LKU: usize = 5;
pub const LKD: usize = 6;
pub const LM1: usize = 7;
pub const LK1: usize = 8;
pub const LM2: usize = 9;
pub const LK2: usize = 10;
/// `klSh`: the line `s` used by a position's margin.
pub const LKSH: usize = 11;
/// `klRp`: the RoPE flag.
pub const LKRP: usize = 12;

/// `kl(l, i)`.
pub fn kl(kl: &[u32], l: u64, i: usize) -> u32 {
    kl[KW_ * l as usize + i]
}

/// `klM(l, i)`: word `i` of the MoE layer `l` (l is odd).
pub fn kl_m(kl: &[u32], l_count: u64, l: u64, i: usize) -> u32 {
    kl[KW_ * l_count as usize + 3 * (l / 2) as usize + i]
}

/// `klRp(l)`.
pub fn kl_rp(kl: &[u32], l: u64) -> u32 {
    kl[KW_ * l as usize + LKRP]
}

/// `klSh(l)`.
pub fn kl_sh(kl: &[u32], l: u64) -> u32 {
    kl[KW_ * l as usize + LKSH]
}

/// `ropeC(l, t, i, sine)`: a RoPE table entry, or 0 / 2^cs when the layer has no RoPE.
pub fn rope_c(h: &Hdr, kl: &[u32], l: u64, t: u64, i: u64, sine: bool) -> i64 {
    if l != u64::MAX && kl_rp(kl, l) == 0 {
        return if sine { 0 } else { 1i64 << h.cs };
    }
    let ang = t as f64 * libm::pow(h.theta0 as f64, -2.0 * (i as f64) / (h.dh as f64));
    libm::round((1i64 << h.cs) as f64 * if sine { libm::sin(ang) } else { libm::cos(ang) }) as i64
}

/// The per-layer RoPE shifts, checked (`cp_verify.cpp:1389-1410`).
pub fn kl_checks(h: &Hdr, words: &[u32]) -> Result<()> {
    // Each layer has KW_ words; a MoE layer's record adds three words at `KW_ * L`.
    let need = KW_ * h.l as usize + if h.ne > 0 { 3 * (h.l as usize / 2) } else { 0 };
    if words.len() < need {
        return Err(Refusal::named("KL-length"));
    }
    let p3 = h.ne > 0;
    let f_qk = h.hf[super::stage_layout::KQ_] as i32;
    let f_v = h.hf[super::stage_layout::KV_] as i32;
    let f_o = h.hf[super::stage_layout::KO_] as i32;
    let f_g = h.hf[super::stage_layout::KGD] as i32;
    let f_u = h.hf[super::stage_layout::KUD] as i32;
    let f_d = h.hf[super::stage_layout::KDD] as i32;
    let f_r = h.hf[super::stage_layout::KR_] as i32;
    let rng = |k: u32, form: i32| -> Result<()> {
        let hi = if form == 0 { 16 } else if form == 1 { 24 } else { 32 };
        if k < 1 || k > hi {
            return Err(Refusal::named("KL-shift-range"));
        }
        Ok(())
    };
    for l in 0..h.l as u64 {
        rng(kl(words, l, LKG), f_g)?;
        rng(kl(words, l, LKU), f_u)?;
        rng(kl(words, l, LKD), f_d)?;
        rng(kl(words, l, LKQ), f_qk)?;
        rng(kl(words, l, LKK), f_qk)?;
        rng(kl(words, l, LKV), f_v)?;
        rng(kl(words, l, LKO), f_o)?;
        if kl(words, l, LKQ) != kl(words, l, LKK) && (kl(words, l, LKQ) < 16 || kl(words, l, LKK) < 16) {
            return Err(Refusal::named("KL-kq-kk"));
        }
        for n in 0..2 {
            let m = kl(words, l, if n == 1 { LM2 } else { LM1 });
            let k = kl(words, l, if n == 1 { LK2 } else { LK1 });
            if m < 24 || m > 47 || k + 14 < m || k < 17 || k > 32 {
                return Err(Refusal::named("KL-norm"));
            }
        }
        if kl_rp(words, l) > 1 {
            return Err(Refusal::named("KL-rp"));
        }
        if p3 && l % 2 == 1 {
            rng(kl_m(words, h.l as u64, l, 0), f_r)?;
            rng(kl_m(words, h.l as u64, l, 1), f_g)?;
            rng(kl_m(words, h.l as u64, l, 2), f_u)?;
        }
    }
    Ok(())
}

/// `tails[g]`: the matrices of layer sub-proof `g`'s range check.
pub fn build_tails(y: &Lay, h: &Hdr, ngr: u64) -> Vec<Tail> {
    let mut tails = vec![Tail::default(); ngr as usize];
    for g in 0..ngr {
        let t = &mut tails[g as usize];
        let gid = 1 + g;
        let mut req = |name: String, m: u64, k: u64| {
            let mut mat = TMat::default();
            mat.name = name;
            mat.m = m;
            mat.k = k;
            mat.a_id = gid * 256 + t.mats.len() as u64;
            t.mats.push(mat);
        };
        for p in 0..y.parts[0] {
            req(format!("af{}", p), y.mrow[0], y.kcol[0]);
        }
        for p in 0..y.parts[1] {
            req(format!("ad{}", p), y.mrow[1], y.kcol[1]);
        }
        req(String::from("ar"), y.mrow[2], y.kcol[2]);
        req(String::from("b"), 1u64 << h.lmb, y.kbm);
        req(String::from("qa"), y.mrow[3], y.kcol[3]);
        req(String::from("xbO"), y.mxb, y.kxb);
        req(String::from("xbI"), y.mxb, y.kxb);
    }
    let i_ad = y.parts[0] as usize;
    let i_b = i_ad + y.parts[1] as usize + 1;
    let i_qa = i_b + 1;
    let i_xo = i_qa + 1;
    let i_xi = i_xo + 1;
    let _ = i_ad;
    for g in 1..ngr as usize {
        tails[g].mats[i_xi].kind = 1;
        tails[g].mats[i_xi].foreign = 0;
        tails[g].mats[i_xi].a_id = tails[g - 1].mats[i_xo].a_id;
    }
    tails
}

/// `tokenFactorTaken`.
pub fn token_factor_taken(v: u64, lk_w: u32) -> bool {
    let c = ceil_log2(v);
    c >= 1 && c <= lk_w
}

/// `tokenFactorUnits`.
pub fn token_factor_units(lay: &WsLay) -> Result<()> {
    for u in &lay.u {
        if u.x == 12 || u.x == 13 {
            let mut any = false;
            for g in &u.g {
                if g.cls == b'A' {
                    any = true;
                    let c = ceil_log2(g.r) as i32;
                    if c < 1 || c > lay.lk || !g.a_taken() {
                        return Err(Refusal::named("w-list-token-factor"));
                    }
                }
            }
            if !any {
                return Err(Refusal::named("w-list-token-factor"));
            }
        }
    }
    Ok(())
}

/// `wsLay`: W's layout from the statement and the layer layout.
pub fn build_ws_lay(h: &Hdr, y: &Lay, lk_w: u32) -> Result<WsLay> {
    let mut s = WsShape::default();
    s.dd = h.dd;
    s.l = h.l as u64;
    s.d = h.d;
    s.dh = h.dh;
    s.dkv = y.dkv;
    s.dq = y.dq;
    s.f = h.f;
    s.fe = h.fe;
    s.ne = h.ne;
    s.v = h.v;
    s.eh = 1;
    ws_set_moe(&mut s, h.ne > 0);
    if ceil_log2(h.v) > lk_w {
        return Err(Refusal::named("hid-vocab-cols"));
    }
    if !token_factor_taken(h.v, lk_w) {
        return Err(Refusal::named("w-list-token-factor"));
    }
    let mut lay = WsLay::default();
    lay.build(&s, lk_w)?;
    token_factor_units(&lay)?;
    Ok(lay)
}

/// The output head's layout (`struct HL`).
#[derive(Clone, Debug, Default)]
pub struct Hl {
    pub jv: u64,
    pub jva: u64,
    pub oe: u64,
    pub feat: u64,
    pub filled: u64,
    pub k: u64,
    pub m: u64,
    pub oaw: u64,
    pub ora: u64,
    pub od1: u64,
    pub od2: u64,
    pub filld: u64,
    pub kd: u64,
    pub md: u64,
    pub fillr: u64,
    pub kr: u64,
    pub mr: u64,
    pub kb: u64,
    pub calls: Vec<CallD>,
    pub tau_fe: Vec<u64>,
    pub fs: HForest,
}

/// `HLy`: the output head's matrices, calls and lookup forest, with its no-wrap conditions.
pub fn build_hl(
    h: &Hdr,
    y: &Lay,
    pc_h: &[Vec<String>],
    state: &StageState,
) -> Result<Hl> {
    let d = h.d;
    let t = y.t;
    let s2 = y.s2;
    let lt = h.lt;
    let la = h.la;
    let ls = y.ls;
    let vv = h.v;
    let mut l = Hl::default();
    if h.mf < 24 || h.mf > 47 || h.kf + 14 < h.mf {
        return Err(Refusal::named("policy-norm-F"));
    }
    if h.kf < 17 || h.kf > 32 || h.epsf < 1 || h.epsf >= (1u64 << 59) {
        return Err(Refusal::named("policy-norm-F"));
    }
    if h.toksrc != 1 {
        return Err(Refusal::named("policy-toksrc"));
    }
    if h.theta > h.clipc || h.cap as u64 > t || (h.cap as u64) >= (1u64 << 16) {
        return Err(Refusal::named("policy-gap-words"));
    }
    if h.famf != 24 || h.logs > 63 {
        return Err(Refusal::named("policy-gap-words"));
    }
    if h.digsh < 7
        || h.digsh > 8
        || (h.tabs + 4 != h.digsh
            && (h.tabs < h.digsh + 4 || h.tabs > h.digsh + 10))
    {
        return Err(Refusal::named("policy-gap-words"));
    }
    l.jv = (vv + s2 - 1) / s2 * s2;
    l.oaw = 0;
    l.ora = 2 * d;
    l.od1 = 4 * d;
    l.od2 = 4 * d + 2 * l.jv;
    l.oe = 4 * d + 3 * l.jv;
    l.feat = 4 * d + (3 + EXC as u64) * l.jv;
    l.jva = 1u64 << (ceil_log2(l.jv) - 1);
    if l.jva % s2 != 0 || 2 * vv > (1u64 << h.famf) {
        return Err(Refusal::named("policy-gap-words"));
    }
    if h.lmhf < la || h.lmhf > 24 || h.nhf == 0 || h.nhf > 64 || h.lmhd < lt || h.lmhd > 24
        || h.lmhr < lt || h.lmhr > 24 || h.lmbh > 24
    {
        return Err(Refusal::named("shape-request-matrix-H"));
    }
    l.m = 1u64 << h.lmhf;
    {
        let unit = h.nhf as u64 * (l.m / t);
        l.filled = (l.feat + unit - 1) / unit * unit;
        l.k = l.filled / unit;
    }
    l.md = 1u64 << h.lmhd;
    {
        let unit = l.md / t;
        l.filld = (2 * d + unit - 1) / unit * unit;
        l.kd = l.filld / unit;
    }
    l.mr = 1u64 << h.lmhr;
    {
        let unit = l.mr / t;
        l.fillr = (led_nrh(state.residual_stream_limbs) as u64 + unit - 1) / unit * unit;
        l.kr = l.fillr / unit;
    }
    #[derive(Clone)]
    struct SdH {
        name: &'static str,
        kind: &'static str,
        n: u64,
    }
    let mut sd: Vec<SdH> = Vec::new();
    fn push(sd: &mut Vec<SdH>, name: &'static str, kind: &'static str, n: u64) {
        sd.push(SdH { name, kind, n });
    }
    push(&mut sd, "NF", "R16", d);
    push(&mut sd, "NFH", "R16", d);
    push(&mut sd, "HD0", "R16", l.jv);
    push(&mut sd, "HD1", "R16", l.jv);
    push(&mut sd, "ROW", "R8", led_nrh(state.residual_stream_limbs) as u64);
    push(&mut sd, "HD2", "R8", l.jv);
    push(&mut sd, "CNF", "FC", d);
    push(&mut sd, "HE0", "FE", l.jva);
    push(&mut sd, "HE1", "FE", l.jv - l.jva);
    let mut cl: Vec<Vec<String>> = pc_h.to_vec();
    if cl.is_empty() {
        let mk = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        cl = vec![
            mk(&["R16a", "R16", "NF", "NFH", "HD0"]),
            mk(&["R16b", "R16", "HD1"]),
            mk(&["R8", "R8", "ROW", "HD2"]),
            mk(&["FEa", "FE", "HE0"]),
            mk(&["FEb", "FE", "HE1"]),
            mk(&["FC", "FC", "CNF"]),
        ];
    }
    if cl.len() > 6 {
        return Err(Refusal::named("policy-call-list-H"));
    }
    {
        const NQ: [u64; 7] = [
            4034748383, 4162825045, 4228380000, 4261543596, 4278222806, 4286586875, 4290775040,
        ];
        let n = if h.tabs < h.digsh { 484 } else { NQ[(h.tabs - h.digsh - 4) as usize] };
        l.tau_fe = vec![0; 65536];
        let mut g: u128 = 1u128 << (h.famf + 17);
        for u in 0..65536usize {
            l.tau_fe[u] = u as u64 + (((g + 131071) >> 17) as u64) * (1u64 << 16);
            g = (g * n as u128 + 0xFFFF_FFFF) >> 32;
        }
    }
    let mut seen = vec![false; sd.len()];
    for ln in &cl {
        if ln.len() < 3 {
            return Err(Refusal::named("policy-call-list-H"));
        }
        let mut cd = CallD::default();
        cd.c.name = ln[0].clone();
        cd.kind = ln[1].clone();
        if l.calls.iter().any(|o| o.c.name == ln[0]) {
            return Err(Refusal::named("policy-call-list-H"));
        }
        for name in &ln[2..] {
            let mut j = 0usize;
            while j < sd.len() && sd[j].name != name {
                j += 1;
            }
            if j == sd.len() || seen[j] || sd[j].kind != ln[1] {
                return Err(Refusal::named("policy-call-list-H"));
            }
            seen[j] = true;
            cd.segs.push(Seg {
                name: sd[j].name.to_string(),
                n: sd[j].n,
                pos: Vec::new(),
                moe: false,
            });
        }
        l.calls.push(cd);
    }
    if seen.iter().any(|&s| !s) {
        return Err(Refusal::named("policy-call-list-H"));
    }
    let nmin_h = if state.nminh != 0 { state.nminh } else { h.nmin as i32 };
    for q in 0..l.calls.len() {
        let mut cd = l.calls[q].clone();
        let fl = nmin_h - lt as i32;
        place(&mut cd, fl.max(0));
        cd.c.n = cd.l_j + lt as i32;
        cd.c.kappa = 5;
        cd.c.k = if cd.kind == "R8" { 8 } else { 16 };
        if cd.kind == "FC" {
            cd.c.func = 1;
            cd.c.t0 = 32768;
            cd.c.tau = Some(y.tau_fc.clone());
        }
        if cd.kind == "FE" {
            cd.c.func = 1;
            cd.c.t0 = 0;
            cd.c.tau = Some(l.tau_fe.clone());
            if l.tau_fe.len() != 65536 {
                return Err(Refusal::internal("internal-table-FE"));
            }
        }
        if cd.c.n < 10 || cd.c.n < nmin_h || cd.c.n > 44 {
            return Err(Refusal::named(&format!("shape-call-H-{}", cd.c.name)));
        }
        if cd.c.n < la as i32 || cd.l_j < ls {
            return Err(Refusal::named(&format!("shape-call-H-{}", cd.c.name)));
        }
        l.calls[q] = cd;
    }
    {
        let calls: Vec<super::common::Call> = l.calls.iter().map(|c| c.c.clone()).collect();
        let mut fs = forest_shape(&calls, state.lidb)?;
        if fs.d_t < la as i32 {
            return Err(Refusal::named("forest-depth-H"));
        }
        l.kb = forest_plane_cols(&fs, h.lmbh as i32)?;
        for q in 0..l.calls.len() {
            if h.iotah[q] as i64 != fs.iota[q] as i64 {
                return Err(Refusal::named(&format!("shape-call-H-{}", l.calls[q].c.name)));
            }
            l.calls[q].c.iota = fs.iota[q];
        }
        fs.pub_ = vec![0; fs.nt as usize];
        let cs = fs.d_t - lt as i32;
        for q in 0..l.calls.len() {
            let cd = &l.calls[q];
            if (cd.j >> cs) != (1u64 << fs.iota[q]) {
                return Err(Refusal::internal("internal-forest-place"));
            }
            let first = fs.first[q] as usize;
            for j in 0..cd.j as usize {
                if cd.used[j] == 0 {
                    fs.pub_[first + (j >> cs)] += t;
                }
            }
            for s in &cd.segs {
                if s.name.starts_with('H') {
                    let v0 = if s.name == "HE1" { l.jva } else { 0 };
                    let start = if vv > v0 { vv - v0 } else { 0 };
                    for x in start..s.n {
                        fs.pub_[first + (s.pos[x as usize] >> cs) as usize] += t;
                    }
                }
            }
        }
        let names = fs.names.clone();
        let pub_ = fs.pub_.clone();
        forest_pub_ask(&fs, &names, &pub_, "")?;
        l.fs = fs;
    }
    for q in l.calls.len()..6 {
        if h.iotah[q] != 0 {
            return Err(Refusal::named("header-absent-call-H"));
        }
    }
    // The head's no-overflow conditions.
    {
        let ty: u128 = 1u128 << (1 + crate::verifier::common::LBZ);
        let p2: u128 = 1u128 << 60;
        let ty2 = ty * 257;
        let tyx = ty * if state.residual_stream_limbs == 5 { 4311810305u128 } else { 16843009 };
        let bw = WEIGHT_BOUND as u128;
        let bch = (CLAMP as u128) + 1;
        let pw = |k: u32| -> u128 { 1u128 << k };
        let need = |ok: bool, n: &str| -> Result<()> {
            if ok {
                Ok(())
            } else {
                Err(Refusal::named(&format!("no-wrap-H-{}", n)))
            }
        };
        need((pw(16) << h.kf) <= p2, "U-NF")?;
        need(
            pw(h.mf)
                + pw(if state.residual_stream_limbs == 5 { 38 } else { 29 })
                + pw(h.kf - 1)
                + (pw(15) << h.kf)
                + pw(16) * (ty2 + 32896)
                < p2,
            "W-NF",
        )?;
        let sh = 2 * d as u128 * bch * bw + 1;
        need(pw(8) + pw(h.digsh + 16) + pw(h.digsh + 31) <= pw(40), "W-HD0")?;
        need(
            sh + pw(40) + pw(8) * BIGH as u128 + pw(h.digsh) * (ty2 + 32896) + (ty + 128) < p2,
            "W-HD0",
        )?;
        need(
            sh <= BIGH as u128
                && sh + BIGH as u128 + pw(32) <= (pw(16) + 1) * pw(h.digsh + 15),
            "three-digits",
        )?;
        need(BIGH as u128 >= sh + pw(h.digsh + 15), "three-digits")?;
        let r256 = (pw(8 * EXC as u32) - 1) / 255;
        let be = ty * r256 + 128 * r256 + 1;
        need(pw(16) * (be + pw(h.famf) + 1) + pw(16) < p2, "HE")?;
        need(
            l.jv as u128 * pw(h.famf) + pw(8 * EXC as u32) + (l.jv - vv + 1) as u128 * pw(h.famf) < p2,
            "Z",
        )?;
        need(
            t as u128 * (pw(40) + pw(8) * h.clipc as u128 + pw(40)) + (h.theta as u128) * (t as u128) < p2,
            "E2",
        )?;
        need(t as u128 * (pw(8) + pw(16)) + (h.cap as u128) < p2, "E3")?;
        need(pw(40) + pw(40) + (h.clipc as u128) < p2, "E4")?;
        need(tyx + pw(crate::verifier::common::LBZW as u32 + 1) * 16843009 < p2, "J-E")?;
        need(
            (ty2 + 32768) + ((ty2 + core::cmp::max(bch, 4096) as u128) << 28) < p2 / 2
                && ty2 + 32768 + 65536 < pw(28),
            "guard-radix",
        )?;
    }
    for c in &l.calls {
        if c.c.kappa != 5 {
            return Err(Refusal::named(&format!("hid-planes-{}", c.c.name)));
        }
    }
    Ok(l)
}

/// The output head's `Ty` bound: `2^(1 + LBZ)`.
pub fn ty_req() -> u128 {
    1u128 << (1 + crate::verifier::common::LBZ)
}

/// A `KCAP` re-export used by the layout docs: the number of columns a range-check matrix may have.
pub const MATRIX_COLUMN_CAP: u64 = KCAP;
