//! Replay of `scripts/cpp_vectors/weights_vectors.cpp`: the norm digit rows
//! (`verifier/src/vf_norm_digit_rows.h`) and the weight layout and claims
//! (`verifier/src/vf_weights_layout.h`).

use fp_core::field::ext::{E, F};
use fp_core::verifier::common::mix64;
use fp_core::verifier::norm_digit_rows::{
    led_lines, led_lines5, led_mu, led_nr, led_nrh, led_np, led_ns, led_no, led_products5, row5,
    BIGH, EXC, LEDG, LEDNE,
};
use fp_core::verifier::weights_layout::{
    ws_claim_shape, ws_eps_t, ws_gamma_add, ws_row_part, ws_set_moe, WsClaim, WsFac, WsShape,
};
use fp_core::verifier::weights_merge::ws_fork_slots;

const VECTORS: &str = include_str!("../../fixtures/weights_vectors.txt");

fn eb(v: u64) -> E {
    E::from_base(F::from_u64(v))
}

fn exs(x: &E) -> String {
    format!("{:016x},{:016x},{:016x}", x.0[0].0, x.0[1].0, x.0[2].0)
}

fn vecs(v: &[E]) -> String {
    v.iter().map(exs).collect::<Vec<_>>().join(";")
}

fn hash64(v: &[E]) -> u64 {
    let mut h = 0u64;
    for x in v {
        for c in x.0 {
            h = mix64(h.wrapping_add(c.0));
        }
    }
    h
}

fn main_lines() -> Vec<String> {
    let mut out = Vec::new();
    for limbs in [4i32, 5] {
        out.push(format!(
            "NORM limbs={} ns={} nr={} np={} no={} lines={} nrh={}",
            limbs,
            led_ns(limbs),
            led_nr(limbs),
            led_np(limbs),
            led_no(limbs),
            led_lines(limbs),
            led_nrh(limbs)
        ));
        let mut mu = String::new();
        for i in 0..if limbs == 5 { 99 } else { 74 } {
            let m = led_mu(i, limbs);
            if m != 1 {
                mu.push_str(&format!("{}:{};", i, m));
            }
        }
        out.push(format!("NORM mu={}", mu));
    }
    let ledg = LEDG
        .iter()
        .enumerate()
        .map(|(i, x)| format!("{}{}:{}", if i > 0 { "," } else { "" }, x[0], x[1]))
        .collect::<String>();
    out.push(format!(
        "NORM consts LEDNE={} EXC={} BIGH={} LEDG={}",
        LEDNE, EXC, BIGH, ledg
    ));
    {
        let r = row5::<E, _>(|j| eb(((j * 7 + 3) % 251) as u64));
        out.push(format!("ROW5 dg={}", vecs(&r.dg)));
        out.push(format!(
            "ROW5 c={} vlo={} vhi={} a={} b={} sig={} s0={} l1={} h1={} blo={} bhi={} kap={} rlo={} rhi={} R={} q1={} rr={} rq={}",
            vecs(&r.c),
            exs(&r.vlo),
            exs(&r.vhi),
            exs(&r.a),
            exs(&r.b),
            exs(&r.sig),
            exs(&r.s0),
            exs(&r.l1),
            exs(&r.h1),
            exs(&r.blo),
            exs(&r.bhi),
            exs(&r.kap),
            exs(&r.rlo),
            exs(&r.rhi),
            exs(&r.r),
            exs(&r.q1),
            exs(&r.rr),
            exs(&r.rq)
        ));
        let mut p = [E::zero(); 7];
        for j in 0..7 {
            p[j] = eb(100 + j as u64);
        }
        let mut o = [E::zero(); 8];
        led_lines5(&r, &p, eb(7), &eb(1u64 << 40), &mut o);
        out.push(format!("LINES5 out={}", vecs(&o)));
        let mut om = [E::zero(); 7];
        for j in 0..7 {
            om[j] = eb(200 + j as u64);
        }
        out.push(format!(
            "PRODUCTS5 v={}",
            exs(&led_products5(&om, eb(11), eb(12), eb(13), eb(14)))
        ));
    }
    {
        let mut s = WsShape::default();
        s.dd = 32;
        s.l = 2;
        s.d = 8;
        s.dh = 4;
        s.dkv = 6;
        s.dq = 6;
        s.f = 10;
        s.fe = 12;
        s.ne = 4;
        s.v = 11;
        s.eh = 1;
        ws_set_moe(&mut s, true);
        let moe: String = s.moe.iter().map(|x| x.to_string()).collect();
        out.push(format!(
            "WSHAPE D={} L={} d={} dh={} dkv={} dq={} f={} fe={} NE={} V={} eh={} MOE={} moe={}",
            s.dd, s.l, s.d, s.dh, s.dkv, s.dq, s.f, s.fe, s.ne, s.v, s.eh, s.moe_flag, moe
        ));
        let mut lay = fp_core::verifier::weights_layout::WsLay::default();
        lay.build(&s, 6).unwrap();
        out.push(format!(
            "WSLAY lk={} m0={} units={}",
            lay.lk,
            lay.m0,
            lay.u.len()
        ));
        for (i, u) in lay.u.iter().enumerate() {
            out.push(format!(
                "WSUNIT i={} X={} l={} nlw={} ncb={} rows={} off={} groups={}",
                i,
                u.x,
                u.l,
                u.nlw,
                u.ncb,
                u.rows,
                u.off,
                u.g.len()
            ));
            for (gi, g) in u.g.iter().enumerate() {
                out.push(format!(
                    "WSGRP i={} gi={} name={} cls={} R={} o={} z={} t={} cb0={} left={} high={} aTaken={}",
                    i,
                    gi,
                    g.name,
                    g.cls as char,
                    g.r,
                    g.o,
                    g.z,
                    g.t,
                    g.cb0,
                    g.left,
                    if g.high { 1 } else { 0 },
                    if g.a_taken() { 1 } else { 0 }
                ));
            }
        }
        let ui = lay.u.iter().position(|u| u.x == 12).unwrap();
        let mut f0 = WsFac::default();
        for i in 0..s.v {
            f0.av.push(eb(1000 + i));
        }
        let mut f1 = WsFac::default();
        f1.hv.push(eb(3));
        f1.pt = vec![eb(7), eb(11), eb(13)];
        let c = WsClaim { ui: ui as u32, f: vec![f0, f1] };
        ws_claim_shape(&lay, &c).unwrap();
        let mut rm = Vec::new();
        for i in 0..lay.lk {
            rm.push(eb(20 + i as u64));
        }
        let eps = ws_eps_t(&lay, &c, &rm);
        let rp = ws_row_part(&lay, &c, eb(17));
        out.push(format!(
            "WSCLAIM ui={} eps={} ka={} recGroups={}",
            ui,
            exs(&eps),
            exs(&rp.ka),
            rp.f.len()
        ));
        for (gi, x) in rp.f.iter().enumerate() {
            out.push(format!(
                "WSCLAIM gi={} HV={} pl={} AV={}",
                gi,
                vecs(&x.hv),
                vecs(&x.pl),
                vecs(&x.av)
            ));
        }
        let mut gam = vec![E::zero(); lay.m0 as usize];
        ws_gamma_add(&mut gam, &lay, &rp, eb(19)).unwrap();
        out.push(format!(
            "WSGAMMA len={} hash={:016x} first={} last={}",
            gam.len(),
            hash64(&gam),
            exs(&gam[0]),
            exs(&gam[gam.len() - 1])
        ));
    }
    for lk in [1i32, 4, 6, 20] {
        out.push(format!(
            "WSFORKSLOTS lk={} slots={}",
            lk,
            ws_fork_slots(lk)
        ));
    }
    out
}

#[test]
fn weights_and_norm_vectors_match_the_cpp_reference() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}
