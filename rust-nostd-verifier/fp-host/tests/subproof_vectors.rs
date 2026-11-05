//! Replay of `scripts/cpp_vectors/subproof_vectors.cpp`: the instantiable parts of the sub-proof
//! engine, the smallness test's packing and planning, the lookup forest, and the PSC row.
//!
//! The fixture `fixtures/subproof_vectors.txt` is the C++ tool's output, byte for byte. Its format
//! is documented at the top of the tool. The transcript-driven calls are not here: they need a
//! chain, and `fp-host/tests/subproof_tests.rs` exercises them on the Rust one.

use fp_core::field::ext::{E, F};
use fp_core::iop::hp::Weight;
use fp_core::verifier::common::Call;
use fp_core::verifier::engine::{power_of_two_at_least, Aff, HFork, HTree, HRow, TreeKind};
use fp_core::verifier::lookup::{
    forest_elems, forest_lins, forest_plane_cols, forest_pub_ask, forest_pub_run, forest_shape,
    order_forest_range, place_z, u_ent, HCallZ, HPiece,
};
use fp_core::verifier::matrices::TMat;
use fp_core::verifier::packing::{
    eq_plain_f, place_p, same_place_f, tie_left, tie_right, PlaceF, ShP, UnscaledEqIterator,
};
use fp_core::verifier::segment::Tail2;
use fp_core::verifier::smallness::{t2_bl, HTailF2, T2Foreign};
use fp_core::verifier::sumcheck::{
    layer_slots, psc_row, round_values, sc3_slots, sumcheck_slots, tsc_slots, Psc, RoundForm,
};

const VECTORS: &str = include_str!("../../fixtures/subproof_vectors.txt");

fn exs(x: &E) -> String {
    format!("{:016x},{:016x},{:016x}", x.0[0].0, x.0[1].0, x.0[2].0)
}

fn eb(v: u64) -> E {
    E::from_base(F::from_u64(v))
}

fn vecs(v: &[E]) -> String {
    v.iter().map(exs).collect::<Vec<_>>().join(";")
}

fn u64s(v: &[u64]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn i32s(v: &[i32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn affs(a: &Aff) -> String {
    let e = a
        .e
        .iter()
        .map(|x| format!("{}:{}:{}:{}", x.tree, x.row, x.idx, exs(&x.coef)))
        .collect::<Vec<_>>()
        .join(";");
    let s = a
        .s
        .iter()
        .map(|x| format!("{}:{}", x.0, exs(&x.1)))
        .collect::<Vec<_>>()
        .join(";");
    format!("c={} e={} s={}", exs(&a.c), e, s)
}

fn basic_fork() -> HFork {
    let mut f = HFork::default();
    f.g = String::from("t:");
    f.slots(8);
    f
}

fn main_lines() -> Vec<String> {
    let mut out = Vec::new();

    // powerOfTwoAtLeast
    for v in [
        0u64,
        1,
        2,
        3,
        4,
        5,
        7,
        8,
        9,
        15,
        16,
        17,
        1 << 20,
        (1u64 << 32) - 1,
        1u64 << 32,
        1u64 << 63,
    ] {
        out.push(format!("POW2 v={} p={}", v, power_of_two_at_least(v)));
    }

    // Aff
    {
        let mut a = Aff::constant(eb(11));
        a.add(&Aff::slot(2), eb(3));
        a.add(&Aff::ent(1, 2, 7), eb(5));
        let mut b = Aff::slot(4) * eb(9);
        b.add(&Aff::constant(eb(13)), eb(2));
        out.push(format!("AFF a={}", affs(&a)));
        out.push(format!("AFF b={}", affs(&b)));
        out.push(format!("AFF sum={}", affs(&(a.clone() + b.clone()))));
        out.push(format!("AFF diff={}", affs(&(a.clone() - b.clone()))));
        out.push(format!("AFF scaled={}", affs(&(a.clone() * eb(7)))));
    }

    // HFork
    {
        let mut f = basic_fork();
        f.hide(0, eb(5), eb(2)).unwrap();
        f.hide(1, eb(7), eb(3)).unwrap();
        f.ls[0] = eb(4);
        f.ls[1] = eb(9);
        f.c0 = eb(11);
        let (mask, c0) = f.settle(2).unwrap();
        out.push(format!("SETTLE ok mask={} c={}", vecs(&mask), exs(&c0)));
    }
    {
        let mut f = basic_fork();
        f.hide(0, eb(5), eb(2)).unwrap();
        f.ls[1] = eb(9);
        let e = f.settle(2).unwrap_err();
        out.push(format!("SETTLE missing slot result={}", e.name()));
    }
    {
        let mut f = basic_fork();
        f.hide(0, eb(5), eb(2)).unwrap();
        let e = f.hide(0, eb(6), eb(3)).unwrap_err();
        out.push(format!("HIDE twice result={}", e.name()));
    }
    {
        let mut f = basic_fork();
        f.batch_by(eb(3)).unwrap();
        out.push(format!(
            "KAP c0={} c1={} c2={} c5={}",
            exs(&f.kap_at(0).unwrap()),
            exs(&f.kap_at(1).unwrap()),
            exs(&f.kap_at(2).unwrap()),
            exs(&f.kap_at(5).unwrap())
        ));
        f.plan_claims = 6;
        f.kap_map = vec![false; 6];
        f.kap_take(2).unwrap();
        let c = f.kap_take(2).unwrap_err();
        out.push(format!("KAP twice result={}", c.name()));
        let d = f.kap_take(6).unwrap_err();
        out.push(format!("KAP high result={}", d.name()));
    }
    {
        let mut f = basic_fork();
        f.trees.push(HTree {
            name: String::from("A"),
            kind: TreeKind::N,
            r: 4,
            k: 3,
            ..HTree::default()
        });
        f.trees[0].rows.push(HRow { l0: 1, l: vec![E::zero(); 3], ..HRow::default() });
        let mut a = Aff::default();
        a.add(&Aff::ent(0, 0, 3), eb(2));
        f.push(eb(5), &a).unwrap();
        out.push(format!(
            "PUSH L={} c0={}",
            vecs(&f.trees[0].rows[0].l),
            exs(&f.c0)
        ));
        let mut bad = Aff::default();
        bad.add(&Aff::ent(0, 0, 0), E::one());
        let c = f.push(E::one(), &bad).unwrap_err();
        out.push(format!("PUSH low result={}", c.name()));
    }
    {
        let mut f = basic_fork();
        f.trees.push(HTree {
            name: String::from("T"),
            kind: TreeKind::N,
            r: 4,
            k: 5,
            ..HTree::default()
        });
        f.trees[0].rows.push(HRow::default());
        for v in [0u64, 1, 4, 5, 19, 20] {
            out.push(format!("UENT x={} {}", v, affs(&u_ent(&f, 0, v).unwrap())));
        }
        let c = u_ent(&f, 0, (1u64 << 32) * 5).unwrap_err();
        out.push(format!("UENT high result={}", c.name()));
    }

    // Packing
    {
        let mut s = ShP::default();
        s.m = 10;
        s.k = 5;
        s.m_s = 4;
        s.j = 1;
        s.c_j = 0;
        s.r = 4;
        s.rr = 4;
        s.rd = 0;
        s.a_x = 2;
        s.k1 = 5;
        s.kc = 5;
        s.a = 1;
        let rows = vec![eb(3), eb(4), eb(5), eb(6)];
        let lo = vec![eb(2)];
        let gam = vec![eb(100), eb(101), eb(102), eb(103), eb(104)];
        let wl = tie_left(&s, &rows, &lo).unwrap();
        let wr = tie_right(&s, &lo, &gam).unwrap();
        out.push(format!(
            "SHAPE m={} k={} mS={} J={} R={} Rr={} K1={} Kc={} aX={}",
            s.m, s.k, s.m_s, s.j, s.r, s.rr, s.k1, s.kc, s.a_x
        ));
        for i in 0..4u64 {
            let p = place_p(&s, i, 3);
            out.push(format!("PLACE iS={} c=3 row={} place={}", i, p.row, p.place));
        }
        out.push(format!("TIE left={}", vecs(&wl)));
        out.push(format!("TIE right={}", vecs(&wr)));
        let ez = vec![eb(2), eb(3), eb(4)];
        out.push(format!(
            "EQPLAIN n=3 idx=5 z={} v={}",
            vecs(&ez),
            exs(&eq_plain_f(&ez, 3, 5))
        ));
        let mut it = UnscaledEqIterator::new(&ez, 3, 5);
        for i in 0..4 {
            out.push(format!("UNSCALED i={} v={}", i, exs(&it.at())));
            it.next();
        }
        let mut o = PlaceF::default();
        let mut r = PlaceF::default();
        o.owner = 0;
        r.owner = 0;
        o.sh = s.clone();
        r.sh = s.clone();
        o.col0 = 0;
        r.col0 = 0;
        o.k = 5;
        r.k = 5;
        o.kk = 5;
        r.kk = 5;
        o.m = 10;
        r.m = 10;
        o.root_index = 0;
        r.root_index = 0;
        o.hb = 1;
        r.hb = 1;
        o.m_s = 4;
        r.m_s = 4;
        o.lanes = 3;
        r.lanes = 3;
        o.pad_rows = 4;
        r.pad_rows = 4;
        o.j = 1;
        r.j = 1;
        o.off = 0;
        r.off = 0;
        o.w = 0;
        r.w = 0;
        out.push(format!("SAMEPLACE equal='{}'", same_place_f(&o, &r)));
        r.owner = 1;
        out.push(format!("SAMEPLACE owner='{}'", same_place_f(&o, &r)));
        r.owner = 0;
        r.hb = 2;
        out.push(format!("SAMEPLACE hb='{}'", same_place_f(&o, &r)));
    }

    // Forest
    {
        let mut a = Call::default();
        a.name = String::from("A");
        a.n = 22;
        a.k = 6;
        a.kappa = 5;
        a.func = 0;
        a.t0 = 0;
        let mut b = Call::default();
        b.name = String::from("B");
        b.n = 20;
        b.k = 5;
        b.kappa = 5;
        b.func = 0;
        b.t0 = 3;
        let cl = [a, b];
        let h = forest_shape(&cl, 22).unwrap();
        out.push(format!(
            "FOREST dT={} kT={} NT={} rK={} NC={} cK={} v={} d={}",
            h.d_t,
            h.k_t,
            h.nt,
            h.r_k,
            h.nc,
            h.c_k,
            h.v(),
            h.d()
        ));
        out.push(format!(
            "FOREST iota={} first={} callOf={} empty={}",
            i32s(&h.iota),
            i32s(&h.first),
            i32s(&h.call_of),
            h.empty_keys()
        ));
        out.push(format!(
            "FOREST padKey0={} padKey1={}",
            exs(&h.pad_key(0)),
            exs(&h.pad_key(1))
        ));
        let mut pub_ = vec![0u64; h.nt as usize];
        forest_pub_run(&h, &mut pub_, 0, 0, 3).unwrap();
        forest_pub_run(&h, &mut pub_, 0, 5, 2).unwrap();
        forest_pub_run(&h, &mut pub_, 1, 0, 4).unwrap();
        forest_pub_run(&h, &mut pub_, 1, 7, 1).unwrap();
        let mut q = h.clone();
        q.pub_ = pub_.clone();
        out.push(format!(
            "FOREST pub={} padding={}",
            u64s(&pub_),
            q.padding()
        ));
        let names = h.names.clone();
        forest_pub_ask(&h, &names, &pub_, "").unwrap();
        out.push(format!(
            "FOREST elems={} lins={} planeCols5={} planeCols11={}",
            forest_elems(&h),
            forest_lins(&h),
            forest_plane_cols(&h, 5).unwrap(),
            forest_plane_cols(&h, 11).unwrap()
        ));
        let order: Vec<i32> = order_forest_range(23, 3).iter().map(|&x| x as i32).collect();
        out.push(format!("FOREST orderRange={}", i32s(&order)));
        let mut bad = pub_.clone();
        bad[0] = (1u64 << h.d_t) + 1;
        let c = forest_pub_ask(&h, &names, &bad, "").unwrap_err();
        out.push(format!("FOREST pubAsk high result={}", c.name()));
        let mut only = pub_.clone();
        only[4] = 1u64 << h.d_t;
        only[0] = 0;
        only[1] = 0;
        only[2] = 0;
        let c = forest_pub_ask(&h, &names, &only, "").unwrap_err();
        out.push(format!("FOREST pubAsk all-padding result={}", c.name()));
    }

    // placeZ
    {
        let mut z = HCallZ::default();
        let mut p0 = HPiece::default();
        p0.tree = 0;
        p0.row = 0;
        p0.r0 = 0;
        p0.rp = 3;
        p0.c0 = 0;
        p0.cp = 5;
        let mut p1 = HPiece::default();
        p1.tree = 0;
        p1.row = 1;
        p1.r0 = 0;
        p1.rp = 1;
        p1.c0 = 0;
        p1.cp = 1;
        z.pc = vec![p0, p1];
        place_z(&mut z, "R10z", 10, 22).unwrap();
        out.push(format!(
            "PLACEZ name={} n={} iota={} k={} kappa={} fn={} t0={} pub={}",
            z.c.name,
            z.c.n,
            z.c.iota,
            z.c.k,
            z.c.kappa,
            z.c.func,
            z.c.t0,
            u64s(&z.c.public)
        ));
        for (i, p) in z.pc.iter().enumerate() {
            out.push(format!(
                "PLACEZ piece={} a={} b={} CP={} off={}",
                i, p.a, p.b, p.c_p, p.off
            ));
        }
    }

    // t2BL
    for r in [160u64, 5, 32, 33, 256] {
        let b = t2_bl(r).unwrap();
        let s = b
            .iter()
            .map(|x| format!("({},{})", x.0, x.1))
            .collect::<Vec<_>>()
            .join(",");
        out.push(format!("T2BL r={} blocks={}", r, s));
    }

    // Smallness: shape, pieces, trees and ties
    {
        let m0 = TMat {
            name: String::from("qa"),
            m: 10,
            k: 5,
            kind: 0,
            ..TMat::default()
        };
        let mats = vec![m0];
        let tx_of = vec![-1i32];
        let ft: Vec<T2Foreign> = Vec::new();
        let has_u = [true, true, true, false];
        let mut t = HTailF2::new();
        t.shape(&mats, &tx_of, &ft, has_u, 160, 22).unwrap();
        out.push(format!(
            "TAIL mz={} NM={} off={} col0={} gtTree={} gtRow={}",
            t.mz,
            t.nm,
            u64s(&t.off),
            u64s(&t.col0),
            i32s(&t.gt_tree.iter().map(|&x| x as i32).collect::<Vec<_>>()),
            i32s(&t.gt_row.iter().map(|&x| x as i32).collect::<Vec<_>>())
        ));
        out.push(format!(
            "TAIL ix U={},{},{},{} PK={} TX={} ZZ={} BZ={} FT={} count={}",
            t.ix.u[0],
            t.ix.u[1],
            t.ix.u[2],
            t.ix.u[3],
            i32s(&t.ix.pk),
            i32s(&t.ix.tx),
            t.ix.zz,
            t.ix.bz,
            i32s(&t.ix.ft),
            t.ix.count
        ));
        out.push(format!(
            "TAIL lins0={} lins3={} elems={} bzCols={} eq0={} eq3={}",
            t.lins(0),
            t.lins(3),
            t.small_elems(),
            t.bz_columns(),
            t.equations(0),
            t.equations(3)
        ));
        for q in 1..=2 {
            out.push(format!(
                "TAIL call{} name={} n={} iota={} k={} kappa={} pub={} pieces={}",
                q,
                t.z[q].c.name,
                t.z[q].c.n,
                t.z[q].c.iota,
                t.z[q].c.k,
                t.z[q].c.kappa,
                u64s(&t.z[q].c.public),
                t.z[q].pc.len()
            ));
            for (i, p) in t.z[q].pc.iter().enumerate() {
                out.push(format!(
                    "TAIL call{} piece={} tree={} row={} r0={} Rp={} c0={} Cp={} CP={} off={} a={} b={}",
                    q, i, p.tree, p.row, p.r0, p.rp, p.c0, p.cp, p.c_p, p.off, p.a, p.b
                ));
            }
        }
        out.push(format!(
            "TAIL f9 dT={} kT={} NT={} rK={} NC={} cK={} pub={} padding={}",
            t.f9.d_t,
            t.f9.k_t,
            t.f9.nt,
            t.f9.r_k,
            t.f9.nc,
            t.f9.c_k,
            u64s(&t.f9.pub_),
            t.f9.padding()
        ));
        let mut f = HFork::default();
        f.g = String::from("t:");
        let mut tail = Tail2::default();
        let n_u = [1u64, 1, 37];
        let a_tx: Vec<u32> = Vec::new();
        t.add_trees(&mut f, &mut tail, n_u, &a_tx, 1, 0).unwrap();
        out.push(format!(
            "TAIL tabFirst={},{} tabLen={},{}",
            t.tab_first[0], t.tab_first[1], t.tab_len[0], t.tab_len[1]
        ));
        for (i, x) in f.trees.iter().enumerate() {
            out.push(format!(
                "TAIL tree={} name={} kind={} R={} K={} rows={} owner={}",
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
        for (mu, s) in t.shp.iter().enumerate() {
            out.push(format!(
                "TAIL shp mu={} m={} k={} mS={} w={} ln={} cJ={} aX={} t={} a={} n={} mk={} P2={} K1={} Kc={} J={} R={} Rd={} Rr={}",
                mu,
                s.m,
                s.k,
                s.m_s,
                s.w,
                s.ln,
                s.c_j,
                s.a_x,
                s.t,
                s.a,
                s.n,
                s.mk,
                s.p2,
                s.k1,
                s.kc,
                s.j,
                s.r,
                s.rd,
                s.rr
            ));
        }
        let rows = vec![eb(3), eb(4), eb(5), eb(6)];
        let lo = vec![E::one()];
        let gam = vec![eb(100), eb(101), eb(102), eb(103), eb(104)];
        let wl = tie_left(&t.shp[0], &rows, &lo).unwrap();
        let wr = tie_right(&t.shp[0], &lo, &gam).unwrap();
        out.push(format!("TAIL tieLeft={}", vecs(&wl)));
        out.push(format!("TAIL tieRight={}", vecs(&wr)));
    }

    // Sumcheck slot counts and pscRow
    for (f, form) in [
        (0, RoundForm::Eq2),
        (1, RoundForm::Sum2),
        (2, RoundForm::Sum3),
        (3, RoundForm::Nodes),
        (4, RoundForm::Eq),
    ] {
        out.push(format!(
            "ROUND form={} values2={} values3={} slots={}",
            f,
            round_values(form, 0),
            round_values(form, 3),
            sumcheck_slots(form, 4, 2, 2, 3)
        ));
    }
    out.push(format!(
        "ROUND layer={} tsc={} sc3={}",
        layer_slots(4),
        tsc_slots(4, 2, 2, 0),
        sc3_slots(4, 2)
    ));
    {
        let mut f = HFork::default();
        f.g = String::from("t:");
        f.slots(8);
        let mut p = Psc {
            started: true,
            first: 0,
            eps: eb(5),
            target: eb(11),
            claim: eb(13),
            ..Psc::default()
        };
        p.vars.push(Weight::equality(eb(7), 3));
        p.vars.push(Weight::plain(2));
        p.r.push(eb(2));
        p.r.push(eb(3));
        p.start = Aff::constant(eb(4));
        let mut kept = Aff::constant(eb(9));
        kept.add(&Aff::slot(6), eb(2));
        let row = psc_row(&mut f, &mut p, eb(17), &kept).unwrap();
        out.push(format!("PSCROW {}", affs(&row)));
        out.push(format!("PSCROW mask={}", vecs(&f.vp)));
    }
    {
        let mut f = HFork::default();
        f.g = String::from("t:");
        f.slots(8);
        let mut p = Psc { started: true, first: 0, eps: E::one(), ..Psc::default() };
        p.vars.push(Weight::equality(E::one(), 2));
        p.r.push(E::one());
        let row = psc_row(&mut f, &mut p, E::zero(), &Aff::default()).unwrap();
        out.push(format!("PSCROW one {}", affs(&row)));
    }

    out
}

#[test]
fn subproof_vectors_match_the_cpp_reference() {
    let mut got = main_lines().join("\n");
    got.push('\n');
    assert_eq!(got, VECTORS);
}

#[test]
fn the_fixture_covers_every_record_kind() {
    // A cheap guard against a fixture that lost a section: every record kind the tool writes.
    for kind in [
        "POW2 ", "AFF ", "SETTLE ", "HIDE ", "KAP ", "PUSH ", "UENT ", "SHAPE ", "PLACE ",
        "TIE ", "EQPLAIN ", "UNSCALED ", "SAMEPLACE ", "FOREST ", "PLACEZ ", "T2BL ", "TAIL ",
        "ROUND ", "PSCROW ",
    ] {
        assert!(VECTORS.contains(kind), "the fixture has no {} record", kind);
    }
}
