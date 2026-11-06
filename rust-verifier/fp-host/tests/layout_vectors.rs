//! Replay of `scripts/cpp_vectors/layout_vectors.cpp`: the parameter statement and the layer
//! layout of `verifier/src/cp_verify.cpp` on the fixture policy.

use fp_core::stage_state::StageState;
use fp_core::verifier::common::mix64;
use fp_core::verifier::lookup::{forest_elems, forest_lins};
use fp_core::verifier::stage_layout::{
    layout, parse_header, pol_prescan, pol_scan, pol_skeleton, Hdr, Lay, PolScan,
};

const VECTORS: &str = include_str!("../../fixtures/layout_vectors.txt");
const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");

fn u64s(v: &[u64]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn i32s(v: &[i32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn u32s(v: &[u32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn hash64(v: &[u64]) -> u64 {
    let mut h = 0u64;
    for &x in v {
        h = mix64(h.wrapping_add(x));
    }
    h
}

fn main_lines() -> Vec<String> {
    let mut out = Vec::new();
    let mut state = StageState::default();
    let mut ps = PolScan::default();
    pol_prescan(&mut ps, POLICY, &mut state).unwrap();
    pol_skeleton(&mut ps, false, &mut state).unwrap();
    pol_scan(&mut ps, POLICY, &mut state).unwrap();
    ps.h = parse_header(&ps.st, &mut state).unwrap();
    let y: Lay = layout(&ps.h, &ps.pol_calls, &state).unwrap();
    let h: &Hdr = &ps.h;
    out.push(format!(
        "STMT prof={} lt={} L={} ll={} d={} H={} Gk={} dh={} f={} fe={} NE={} V={} eps={},{} cs={} theta0={} la={} nmin={} D={} tau={}",
        h.prof, h.lt, h.l, h.ll, h.d, h.h, h.gk, h.dh, h.f, h.fe, h.ne, h.v, h.eps[0], h.eps[1], h.cs, h.theta0,
        h.la, h.nmin, h.dd, h.tau
    ));
    out.push(format!("STMT hf={} ut={}", u32s(&h.hf), h.ut));
    out.push(format!(
        "STMT lmaf={} NAf={} lmad={} NAd={} lmar={} lmb={} lmq={} lmx={}",
        h.lmaf, h.naf, h.lmad, h.nad, h.lmar, h.lmb, h.lmq, h.lmx
    ));
    out.push(format!("STMT wb={} iota={}", u32s(&h.wb), u32s(&h.iota)));
    out.push(format!(
        "STMT lB={} S={} rx={} kFM={} kFD={} lmS={} NAs={} lmh={} lmo={} lmbA={} iotaA0={}",
        h.l_b, h.sx, h.rx, h.kfm, h.kfd, h.lms, h.nas, h.lmh, h.lmo, h.lmba, h.iotaa0
    ));
    out.push(format!(
        "STMT MF={} KF={} epsF={} toksrc={} lmhf={} NHf={} lmhd={} lmhr={} lmbH={} wbH={} iotaH={}",
        h.mf, h.kf, h.epsf, h.toksrc, h.lmhf, h.nhf, h.lmhd, h.lmhr, h.lmbh, u32s(&h.wbh), u32s(&h.iotah)
    ));
    out.push(format!(
        "STMT C={} theta={} cap={} s={} sh={} sT={} F={} yTok={}",
        h.clipc, h.theta, h.cap, h.logs, h.digsh, h.tabs, h.famf, h.ytok
    ));
    out.push(format!(
        "STMT target at={} hb={}",
        state.stated_target.at, state.stated_target.hb
    ));
    out.push(format!(
        "OPT lidb={} nminh={} rcl={} gcl={} limbs={} pow={} pows={} powc={} eg={} smax={}",
        state.lidb,
        state.nminh,
        state.rcl,
        state.gcl,
        state.residual_stream_limbs,
        state.pow,
        state.pows,
        state.powc,
        state.gate_table_input_fraction_bits,
        state.smax
    ));
    out.push(format!(
        "LAY T={} Lam={} NGr={} Pd={} Pf={} S2={} NW={} NN={} NI={} dq={} dkv={} nqk={} lPf={} lfe={} lPd={} ls={} ldh={} LamM={} lNE={} kbm={}",
        y.t, y.lam, y.ngr, y.pd, y.pf, y.s2, y.nw, y.nn, y.ni, y.dq, y.dkv, y.nqk, y.l_pf, y.lfe, y.l_pd,
        y.ls, y.ldh, y.lam_m, y.l_ne, y.kbm
    ));
    out.push(format!(
        "LAY arrays feat={},{},{},{} filled={},{},{},{} kcol={},{},{},{} mrow={},{},{},{} parts={},{},{},{}",
        y.feat[0], y.feat[1], y.feat[2], y.feat[3],
        y.filled[0], y.filled[1], y.filled[2], y.filled[3],
        y.kcol[0], y.kcol[1], y.kcol[2], y.kcol[3],
        y.mrow[0], y.mrow[1], y.mrow[2], y.mrow[3],
        y.parts[0], y.parts[1], y.parts[2], y.parts[3]
    ));
    out.push(format!(
        "LAY xb xbFilled={} kxb={} mxb={} off={} nl={} cnt={} J={}",
        y.xb_filled, y.kxb, y.mxb, y.xb.off, y.xb.nl, y.xb.cnt, y.xb.j
    ));
    for (i, t) in y.ten.iter().enumerate() {
        out.push(format!(
            "TEN i={} name={} mat={} nl={} cnt={} J={} OFF={}",
            i, t.name, t.mat, t.nl, t.cnt, t.j, t.off
        ));
    }
    for (i, k) in y.kinds.iter().enumerate() {
        out.push(format!(
            "KIND i={} idx={} name={} L={} segs={}",
            i, k.idx, k.name, k.l, k.segs
        ));
    }
    out.push(format!(
        "TAU fc={:016x} fl={:016x} fs={:016x} lens={},{},{}",
        hash64(&y.tau_fc),
        hash64(&y.tau_fl),
        hash64(&y.tau_fs),
        y.tau_fc.len(),
        y.tau_fl.len(),
        y.tau_fs.len()
    ));
    for (q, c) in y.calls.iter().enumerate() {
        let segs = c
            .segs
            .iter()
            .map(|s| format!("{}:{}:{}", s.name, s.n, if s.moe { 1 } else { 0 }))
            .collect::<Vec<_>>()
            .join(";");
        out.push(format!(
            "CALL q={} name={} kind={} n={} iota={} kappa={} k={} fn={} t0={} lJ={} J={} segs={}",
            q, c.c.name, c.kind, c.c.n, c.c.iota, c.c.kappa, c.c.k, c.c.func, c.c.t0, c.l_j, c.j, segs
        ));
        let used: String = c.used.iter().map(|x| x.to_string()).collect();
        out.push(format!("CALL used q={} used={}", q, used));
    }
    let fo = &y.fo;
    out.push(format!(
        "FOREST dT={} kT={} NT={} rK={} NC={} cK={} iota={} first={} callOf={}",
        fo.d_t, fo.k_t, fo.nt, fo.r_k, fo.nc, fo.c_k, i32s(&fo.iota), i32s(&fo.first), i32s(&fo.call_of)
    ));
    out.push(format!(
        "FOREST pub={} padding={} elems={} lins={}",
        u64s(&fo.pub_),
        fo.padding(),
        forest_elems(fo),
        forest_lins(fo)
    ));
    out
}

#[test]
fn the_stage_layout_matches_the_cpp_reference() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}
