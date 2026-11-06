//! Replay of `scripts/cpp_vectors/attention_vectors.cpp`: `verifier/src/vf_attention_shape.h`
//! and `aforkShapeHid()` of `verifier/src/vf_attention_check.h`.
//!
//! The fixture `fixtures/attention_vectors.txt` is the C++ tool's output, byte for byte.

use fp_core::field::ext::{E, F};
use fp_core::verifier::attention_shape::{
    afork_shape_hid, block_row, block_rows, cut_last, eq_at, eq_pts, head_feat, hi_tab, id_of,
    last_of, le_of, long_phi, long_point, ones_of, ten_cell, ACall, ACfg, AFork, Line, TenAt,
    CLAMP, CLAMPED_CELL_BOUND, S_FD, S_FM, S_IX, S_RD, S_RM, S_WH, S_WL,
};
use fp_core::verifier::common::mix64;
use fp_core::verifier::lookup::{forest_elems, forest_lins};

const VECTORS: &str = include_str!("../../fixtures/attention_vectors.txt");

fn eb(v: u64) -> E {
    E::from_base(F::from_u64(v))
}

fn exs(x: &E) -> String {
    format!("{:016x},{:016x},{:016x}", x.0[0].0, x.0[1].0, x.0[2].0)
}

fn vecs(v: &[E]) -> String {
    v.iter().map(exs).collect::<Vec<_>>().join(";")
}

fn i32s(v: &[i32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn u64s(v: &[u64]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn hash64(v: &[u64]) -> u64 {
    let mut h = 0u64;
    for &x in v {
        h = mix64(h.wrapping_add(x));
    }
    h
}

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

fn call_line(q: usize, c: &ACall) -> String {
    let mut s = format!(
        "ACALL q={} name={} kind={} sh={} segs={} n={} k={} kappa={} fn={} t0={} tot={} pieces={} tauLen={} tauHash={:016x}",
        q,
        c.c.name,
        c.kind,
        c.sh,
        i32s(&c.segs),
        c.c.n,
        c.c.k,
        c.c.kappa,
        c.c.func,
        c.c.t0,
        c.tot,
        c.pcs.len(),
        c.tau.len(),
        hash64(&c.tau)
    );
    if !c.tau.is_empty() {
        s.push_str(&format!(
            " tauFirst={} tauLast={}",
            u64s(&c.tau[..8.min(c.tau.len())]),
            c.tau[c.tau.len() - 1]
        ));
    }
    s
}

fn main_lines() -> Vec<String> {
    let mut out = Vec::new();
    out.push(format!("CONST clamp={} clamped={}", CLAMP, CLAMPED_CELL_BOUND));

    {
        let x = TenAt { off: 3, nl: 2, cnt: 4, j: 5 };
        out.push(format!("TEN off=3 nl=2 cnt=4 J=5 l=1 i=3 j=4 cell={}", ten_cell(&x, 1, 3, 4)));
        let low = vec![eb(2), eb(3)];
        let tok = vec![eb(4), eb(5), eb(6), eb(7)];
        let br = block_rows(&low, &tok);
        out.push(format!("BLOCKROWS low={} tok={} row={}", vecs(&low), vecs(&tok), vecs(&br)));
        for (i, _) in br.iter().enumerate() {
            out.push(format!(
                "BLOCKROW i={} c2={} t={} idx={}",
                i,
                i / tok.len(),
                i % tok.len(),
                block_row(i / tok.len(), i % tok.len(), tok.len())
            ));
        }
        let lp = long_point(&low, 2, &tok);
        out.push(format!("LONGPOINT p={}", vecs(&lp)));
        let ph = long_phi(&lp, 2, 2);
        out.push(format!("LONGPHI p={}", vecs(&ph)));
        let z = vec![eb(11), eb(12), eb(13), eb(14), eb(15)];
        let cut = cut_last(&z, 5, 2).unwrap();
        out.push(format!(
            "CUT hi={} lo={} nhi={}",
            vecs(cut.hi),
            vecs(cut.lo),
            cut.nhi
        ));
        out.push(format!("LASTOF={}", vecs(&last_of(&z, 2).unwrap())));
        for la in 1..=3 {
            out.push(format!(
                "HITAB la={} want={} v={}",
                la,
                5 - la,
                vecs(&hi_tab(&z, la as usize, (5 - la) as usize).unwrap())
            ));
        }
        let hx = TenAt { off: 0, nl: 1, cnt: 1, j: 8 };
        out.push(format!(
            "HEADFEAT hd=0 dh=4 first={} hd=1 dh=4 first={}",
            head_feat(&hx, 0, 4).unwrap(),
            head_feat(&hx, 1, 4).unwrap()
        ));
    }
    {
        let x = vec![eb(2), eb(3), eb(4)];
        let y = vec![eb(5), eb(6), eb(7)];
        out.push(format!("EQAT n=3 idx=5 v={}", exs(&eq_at(&x, 3, 5))));
        out.push(format!("EQPTS n=3 v={}", exs(&eq_pts(&x, &y, 3))));
        out.push(format!("ONES n=3 v={}", exs(&ones_of(&x, 3))));
        out.push(format!("IDOF n=3 v={}", exs(&id_of(&x, 3))));
        out.push(format!("LEOF x<=y v={}", exs(&le_of(&x, &y, 3))));
        out.push(format!("LEOF y<=x v={}", exs(&le_of(&y, &x, 3))));
    }

    let mut a = AFork { cf: config(), ..AFork::default() };
    a.shape().unwrap();
    out.push(format!(
        "ASHAPE T={} B={} nT={} hP={} G={} HA={} dh={} dq={} dkv={} Lam={} u0={}",
        a.t, a.b, a.n_t, a.h_p, a.g, a.ha, a.dh, a.dq, a.dkv, a.lam, a.u0
    ));
    out.push(format!(
        "ASHAPE lnT={} nM={} nD={} ls={} Smax={} kAs={} kbA={}",
        a.ln_t, a.n_m, a.n_d, a.ls, a.smax, a.k_as, a.kb_a
    ));
    out.push(format!(
        "ASHAPE featH={} featO={} featQ={} fillH={} fillO={} fillQ={}",
        a.feat_h, a.feat_o, a.feat_q, a.fill_h, a.fill_o, a.fill_q
    ));
    out.push(format!(
        "ASHAPE oMr={} oZr={} oIb={} oRh={} oRhp={} oQ={} oK={} oV={} oO={}",
        a.o_mr, a.o_zr, a.o_ib, a.o_rh, a.o_rhp, a.o_q, a.o_k, a.o_v, a.o_o
    ));
    out.push(format!(
        "ASHAPE atQ={},{},{},{} atK={},{},{},{} atV={},{},{},{} atO={},{},{},{}",
        a.at_q.off, a.at_q.nl, a.at_q.cnt, a.at_q.j,
        a.at_k.off, a.at_k.nl, a.at_k.cnt, a.at_k.j,
        a.at_v.off, a.at_v.nl, a.at_v.cnt, a.at_v.j,
        a.at_o.off, a.at_o.nl, a.at_o.cnt, a.at_o.j
    ));
    out.push(format!(
        "ASHAPE tt={} u0={} first={} hash={:016x} last={}",
        a.tt.len(),
        a.u0,
        u64s(&a.tt[..8.min(a.tt.len())]),
        hash64(&a.tt),
        a.tt[a.tt.len() - 1]
    ));
    out.push(format!("ASHAPE tableWords={}", a.table_words()));
    for (q, c) in a.calls.iter().enumerate() {
        out.push(call_line(q, c));
        for (i, pc) in c.pcs.iter().enumerate() {
            out.push(format!(
                "APIECE q={} i={} seg={} lam={} a={} b={} off={}",
                q, i, pc.seg, pc.lam, pc.a, pc.b, pc.off
            ));
        }
    }

    let mut b = AFork { cf: config(), ..AFork::default() };
    let h = afork_shape_hid(&mut b, 22).unwrap();
    out.push(format!(
        "AFOREST kbA={} dT={} kT={} NT={} rK={} NC={} cK={} iota={} first={} callOf={}",
        b.kb_a,
        h.d_t,
        h.k_t,
        h.nt,
        h.r_k,
        h.nc,
        h.c_k,
        i32s(&h.iota),
        i32s(&h.first),
        i32s(&h.call_of)
    ));
    out.push(format!(
        "AFOREST pub={} padding={} elems={} lins={}",
        u64s(&h.pub_),
        h.padding(),
        forest_elems(&h),
        forest_lins(&h)
    ));
    for (q, c) in b.calls.iter().enumerate() {
        out.push(format!(
            "AFOREST call={} iota={} n={}",
            q, c.c.iota, c.c.n
        ));
    }
    out
}

#[test]
fn attention_shape_vectors_match_the_cpp_reference() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}
