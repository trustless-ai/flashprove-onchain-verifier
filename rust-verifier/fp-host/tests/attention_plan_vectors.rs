//! Replay of `scripts/cpp_vectors/attention_plan_vectors.cpp`: `AttentionSubProof::plan()`
//! (`verifier/src/vf_attention_check.h`) on the synthetic configuration of `attention_vectors`.
//!
//! The fixture `fixtures/attention_plan_vectors.txt` is the C++ tool's output, byte for byte.

use fp_core::verifier::attention_check::{AttentionSubProof, AttentionSubProofInputs};
use fp_core::verifier::attention_shape::{ACfg, AFork, Line, S_FD, S_FM, S_IX, S_RD, S_RM, S_WH, S_WL};
use fp_core::verifier::engine::TreeKind;

const VECTORS: &str = include_str!("../../fixtures/attention_plan_vectors.txt");

fn config() -> ACfg {
    let mut c = ACfg::default();
    c.lt = 4;
    c.l_b = 2;
    c.lgk = 2;
    c.ldh = 2;
    c.ll = 0;
    c.s = 5;
    c.rx = 4;
    c.k_fd = 11;
    c.lm_s = 4;
    c.la = 6;
    c.lmb = 11;
    c.nmin = 10;
    c.h = 8;
    c.sh = vec![5];
    c.wc_h = 4;
    c.wc_o = 4;
    c.wc_q = 8;
    c.n_as = 2;
    c.ty = 1u128 << 18;
    c.o_in_qa = true;
    c.lines = vec![
        Line { name: String::from("KR"), kind: String::from("KR"), segs: vec![S_RM, S_RD] },
        Line { name: String::from("KF"), kind: String::from("KFD"), segs: vec![S_FM, S_FD] },
        Line { name: String::from("R"), kind: String::from("R16"), segs: vec![S_WL, S_IX] },
        Line { name: String::from("W"), kind: String::from("WH"), segs: vec![S_WH] },
    ];
    c
}

fn i32s(v: &[i32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn u64s(v: &[u64]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn main_lines() -> Vec<String> {
    let mut out = Vec::new();
    let mut sp = AttentionSubProof::default();
    sp.a = AFork { cf: config(), ..AFork::default() };
    sp.a.shape().unwrap();
    sp.input = AttentionSubProofInputs {
        hb: 20,
        gid: 1,
        kt_o: sp.a.fill_q / sp.a.cf.wc_q,
        col0_q: 0,
        a_o: 2,
        mid_q: 777,
        wp_s: 0,
        wp_h: 0,
        wp_o: 0,
        wp_b_a: 0,
        wp_q: 0,
        lidb: 22,
        stated_hb: 0,
        // The C++ tool includes cp_verify.cpp, whose file-scope TAU is 160 (`vf_common.h:468`).
        tau: 160,
    };
    sp.plan().unwrap();

    out.push(format!(
        "APLAN nMsg={} nLin={} NC={} NP={} nKRp={} nKFp={} nW={} ns={}",
        sp.n_msg, sp.n_lin, sp.nc, sp.np, sp.n_krp, sp.n_kfp, sp.n_w, sp.ns
    ));
    out.push(format!(
        "APLAN own lt={} lgk={} pairs={} Lam={} plane_messages={} e={} value_m={} value_d={} attained={} bits={} rows={}",
        sp.own.lt,
        sp.own.lgk,
        sp.own.pairs,
        sp.own.lam,
        sp.own.plane_messages,
        sp.own.e,
        sp.own.value_m,
        sp.own.value_d,
        sp.own.attained,
        sp.own.bits,
        sp.own.rows
    ));
    out.push(format!(
        "APLAN score={}",
        sp.own
            .score
            .iter()
            .map(|x| format!("{}:{}", x.0, x.1))
            .collect::<Vec<_>>()
            .join(";")
    ));
    out.push(format!(
        "ASEAM nU={},{},{} tabFirst={},{} tabLen={},{} NM={} pkMat={} pxMat={}",
        sp.seam.n_u[0],
        sp.seam.n_u[1],
        sp.seam.n_u[2],
        sp.seam.tl.tab_first[0],
        sp.seam.tl.tab_first[1],
        sp.seam.tl.tab_len[0],
        sp.seam.tl.tab_len[1],
        sp.seam.tl.nm,
        sp.seam.tl.pk_mat.len(),
        sp.seam.tl.px_mat.len()
    ));
    out.push(format!(
        "ASEAM ix U={},{},{},{} PK={} TX={} ZZ={} BZ={} FT={} count={}",
        sp.seam.tl.ix.u[0],
        sp.seam.tl.ix.u[1],
        sp.seam.tl.ix.u[2],
        sp.seam.tl.ix.u[3],
        i32s(&sp.seam.tl.ix.pk),
        i32s(&sp.seam.tl.ix.tx),
        sp.seam.tl.ix.zz,
        sp.seam.tl.ix.bz,
        i32s(&sp.seam.tl.ix.ft),
        sp.seam.tl.ix.count
    ));
    out.push(format!(
        "ASEAM f9 dT={} kT={} NT={} rK={} NC={} cK={} pub={} padding={} elems={} lins={}",
        sp.seam.tl.f9.d_t,
        sp.seam.tl.f9.k_t,
        sp.seam.tl.f9.nt,
        sp.seam.tl.f9.r_k,
        sp.seam.tl.f9.nc,
        sp.seam.tl.f9.c_k,
        u64s(&sp.seam.tl.f9.pub_),
        sp.seam.tl.f9.padding(),
        sp.seam.tl.small_elems(),
        sp.seam.tl.lins(0)
    ));
    for (mu, m) in sp.seam.tl.mats.iter().enumerate() {
        let s = &sp.seam.tl.shp[mu];
        out.push(format!(
            "AMAT mu={} name={} m={} k={} kind={} foreign={} ttOff={} aId={} wp={} mS={} J={} R={} Rr={} Kc={}",
            mu,
            m.name,
            m.m,
            m.k,
            m.kind,
            m.foreign,
            m.tt_off,
            m.a_id,
            m.wp,
            s.m_s,
            s.j,
            s.r,
            s.rr,
            s.kc
        ));
    }
    for (i, x) in sp.seam.fp.trees.iter().enumerate() {
        out.push(format!(
            "ATREE i={} name={} kind={} R={} K={} rows={} owner={}",
            i,
            x.name,
            match x.kind {
                TreeKind::N => 'N',
                TreeKind::P => 'P',
            },
            x.r,
            x.k,
            x.rows.len(),
            if x.owner { 1 } else { 0 }
        ));
    }
    out.push(format!(
        "APLAN equations={} lins0={}",
        sp.seam.tl.equations(sp.seam.tl.lins(0)),
        sp.seam.tl.lins(0)
    ));
    out
}

#[test]
fn attention_plan_vectors_match_the_cpp_reference() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}
