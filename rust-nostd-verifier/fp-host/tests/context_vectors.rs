//! Replay of `scripts/cpp_vectors/context_vectors.cpp`: KL.bin, the layer range-check matrices,
//! W's layout and the output head's layout, built from the fixture policy.

use fp_core::stage_state::StageState;
use fp_core::verifier::common::mix64;
use fp_core::verifier::stage_context::{
    build_hl, build_tails, build_ws_lay, kl_checks, rope_c,
};
use fp_core::verifier::stage_layout::{layout, parse_header, pol_prescan, pol_scan, pol_skeleton, PolScan};

const VECTORS: &str = include_str!("../../fixtures/context_vectors.txt");
const POLICY: &[u8] = include_bytes!("../../fixtures/config/policy.txt");
const KL_BYTES: &[u8] = include_bytes!("../../fixtures/config/KL.bin");

fn u64s(v: &[u64]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn i32s(v: &[i32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn hash32(v: &[u32]) -> u64 {
    let mut h = 0u64;
    for &x in v {
        h = mix64(h.wrapping_add(x as u64));
    }
    h
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
    let kl: Vec<u32> = KL_BYTES
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    let mut state = StageState::default();
    let mut ps = PolScan::default();
    pol_prescan(&mut ps, POLICY, &mut state).unwrap();
    pol_skeleton(&mut ps, false, &mut state).unwrap();
    pol_scan(&mut ps, POLICY, &mut state).unwrap();
    ps.h = parse_header(&ps.st, &mut state).unwrap();
    let h = &ps.h;
    let y = layout(h, &ps.pol_calls, &state).unwrap();
    kl_checks(h, &kl).unwrap();
    out.push(format!(
        "KL len={} hash={:016x} head={}",
        kl.len(),
        hash32(&kl),
        u64s(&kl[..8.min(kl.len())].iter().map(|&x| x as u64).collect::<Vec<_>>())
    ));
    let ws = build_ws_lay(h, &y, ps.frame.block_log).unwrap();
    out.push(format!("WS lk={} m0={} units={}", ws.lk, ws.m0, ws.u.len()));
    for (i, u) in ws.u.iter().enumerate() {
        out.push(format!(
            "WSUNIT i={} X={} l={} nlw={} ncb={} rows={} off={}",
            i, u.x, u.l, u.nlw, u.ncb, u.rows, u.off
        ));
    }
    let tails = build_tails(&y, h, y.ngr);
    for (g, t) in tails.iter().enumerate() {
        for (i, m) in t.mats.iter().enumerate() {
            out.push(format!(
                "TAIL g={} i={} name={} m={} k={} kind={} foreign={} ttOff={} aId={}",
                g, i, m.name, m.m, m.k, m.kind, m.foreign, m.tt_off, m.a_id
            ));
        }
    }
    let i_ad = y.parts[0] as usize;
    let i_ar = i_ad + y.parts[1] as usize;
    let i_b = i_ar + 1;
    let i_qa = i_b + 1;
    let i_xo = i_qa + 1;
    let i_xi = i_xo + 1;
    out.push(format!(
        "IDX iAF=0 iAD={} iAR={} iB={} iQA={} iXO={} iXI={}",
        i_ad, i_ar, i_b, i_qa, i_xo, i_xi
    ));
    let hl = build_hl(h, &y, &ps.pol_calls_h, &state).unwrap();
    out.push(format!(
        "HL JV={} JVa={} oE={} feat={} filled={} k={} m={} oAw={} oRa={} oD1={} oD2={} fillD={} kD={} mD={} fillR={} kR={} mR={} kb={}",
        hl.jv, hl.jva, hl.oe, hl.feat, hl.filled, hl.k, hl.m, hl.oaw, hl.ora, hl.od1, hl.od2, hl.filld,
        hl.kd, hl.md, hl.fillr, hl.kr, hl.mr, hl.kb
    ));
    out.push(format!(
        "HL tauFE len={} hash={:016x} first={} last={}",
        hl.tau_fe.len(),
        hash64(&hl.tau_fe),
        hl.tau_fe[0],
        hl.tau_fe[hl.tau_fe.len() - 1]
    ));
    for (q, c) in hl.calls.iter().enumerate() {
        let segs = c
            .segs
            .iter()
            .map(|s| format!("{}:{}", s.name, s.n))
            .collect::<Vec<_>>()
            .join(";");
        out.push(format!(
            "HLCALL q={} name={} kind={} n={} iota={} kappa={} k={} fn={} t0={} lJ={} J={} segs={}",
            q, c.c.name, c.kind, c.c.n, c.c.iota, c.c.kappa, c.c.k, c.c.func, c.c.t0, c.l_j, c.j, segs
        ));
    }
    let fo = &hl.fs;
    out.push(format!(
        "HLFOREST dT={} kT={} NT={} rK={} NC={} cK={} iota={} first={} pub={} padding={}",
        fo.d_t,
        fo.k_t,
        fo.nt,
        fo.r_k,
        fo.nc,
        fo.c_k,
        i32s(&fo.iota),
        i32s(&fo.first),
        u64s(&fo.pub_),
        fo.padding()
    ));
    for l in 0..h.l as u64 {
        for (t, i, sine) in [(0u64, 0u64, false), (1, 0, false), (3, 1, true), (y.t - 1, h.dh / 2 - 1, false)] {
            out.push(format!(
                "ROPE l={} t={} i={} sine={} v={}",
                l,
                t,
                i,
                if sine { 1 } else { 0 },
                rope_c(h, &kl, l, t, i, sine)
            ));
        }
    }
    out
}

#[test]
fn the_stage_context_matches_the_cpp_reference() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}
