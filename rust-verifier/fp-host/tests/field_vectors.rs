//! Lane A parity: every line of `fixtures/field_vectors.txt` is produced by
//! `scripts/cpp_vectors/field_vectors.cpp` from the C++ `blocks/field` headers, and is recomputed
//! here with the Rust port.

use fp_core::field::ext::{F, E};
use fp_core::field::gl64;
use fp_core::field::mle;

const VECTORS: &str = include_str!("../../fixtures/field_vectors.txt");

fn hx(s: &str) -> u64 {
    u64::from_str_radix(s, 16).unwrap_or_else(|_| panic!("not hex: {}", s))
}
fn f(s: &str) -> F {
    F(hx(s))
}
fn e_at(t: &[&str], i: usize) -> E {
    E([f(t[i]), f(t[i + 1]), f(t[i + 2])])
}

#[test]
fn field_vectors_match_the_cpp_reference() {
    let mut lines = 0usize;
    for (lineno, line) in VECTORS.lines().enumerate() {
        let t: Vec<&str> = line.split_whitespace().collect();
        assert!(!t.is_empty(), "empty line {}", lineno + 1);
        match t[0] {
            "F" => match t[1] {
                "add" => assert_eq!(f(t[2]) + f(t[3]), f(t[4]), "line {}", lineno + 1),
                "sub" => assert_eq!(f(t[2]) - f(t[3]), f(t[4]), "line {}", lineno + 1),
                "mul" => assert_eq!(f(t[2]) * f(t[3]), f(t[4]), "line {}", lineno + 1),
                "neg" => assert_eq!(-f(t[2]), f(t[3]), "line {}", lineno + 1),
                "inv" => assert_eq!(f(t[2]).inv(), f(t[3]), "line {}", lineno + 1),
                "pow0" => assert_eq!(f(t[2]).pow(0), f(t[3]), "line {}", lineno + 1),
                "pow1" => assert_eq!(f(t[2]).pow(1), f(t[3]), "line {}", lineno + 1),
                "pow5" => assert_eq!(f(t[2]).pow(5), f(t[3]), "line {}", lineno + 1),
                "powP" => assert_eq!(f(t[2]).pow(gl64::P), f(t[3]), "line {}", lineno + 1),
                "from_u64" => assert_eq!(F::from_u64(hx(t[2])), f(t[3]), "line {}", lineno + 1),
                "from_i64" => assert_eq!(F::from_i64(hx(t[2]) as i64), f(t[3]), "line {}", lineno + 1),
                "reduce128" => assert_eq!(
                    gl64::reduce128(hx(t[2]), hx(t[3])),
                    hx(t[4]),
                    "line {}",
                    lineno + 1
                ),
                "dot3" => assert_eq!(
                    gl64::dot3(hx(t[2]), hx(t[3]), hx(t[4]), hx(t[5]), hx(t[6]), hx(t[7])),
                    hx(t[8]),
                    "line {}",
                    lineno + 1
                ),
                op => panic!("unknown F op {} at line {}", op, lineno + 1),
            },
            "E" => match t[1] {
                "add" => assert_eq!(e_at(&t, 2) + e_at(&t, 5), e_at(&t, 8), "line {}", lineno + 1),
                "sub" => assert_eq!(e_at(&t, 2) - e_at(&t, 5), e_at(&t, 8), "line {}", lineno + 1),
                "mul" => assert_eq!(e_at(&t, 2) * e_at(&t, 5), e_at(&t, 8), "line {}", lineno + 1),
                "mulf" => {
                    let a = e_at(&t, 2);
                    let b = e_at(&t, 5);
                    assert_eq!(a * b.0[1], e_at(&t, 8), "line {}", lineno + 1);
                }
                "neg" => assert_eq!(-e_at(&t, 2), e_at(&t, 5), "line {}", lineno + 1),
                "inv" => assert_eq!(e_at(&t, 2).inv(), e_at(&t, 5), "line {}", lineno + 1),
                "pow0" => assert_eq!(e_at(&t, 2).pow(0), e_at(&t, 5), "line {}", lineno + 1),
                "pow3" => assert_eq!(e_at(&t, 2).pow(3), e_at(&t, 5), "line {}", lineno + 1),
                "powP" => assert_eq!(e_at(&t, 2).pow(gl64::P), e_at(&t, 5), "line {}", lineno + 1),
                "powE" => assert_eq!(
                    e_at(&t, 2).pow(hx(t[5])),
                    e_at(&t, 6),
                    "line {}",
                    lineno + 1
                ),
                "theta" => {
                    let i: usize = t[2].parse().unwrap();
                    assert_eq!(E::theta(i), e_at(&t, 3), "line {}", lineno + 1);
                }
                op => panic!("unknown E op {} at line {}", op, lineno + 1),
            },
            "MLE" if t[1] == "poly_eval" => {
                // The line has no `k`: `MLE poly_eval <d> <x> <coeffs...> <result>`.
                let d: usize = t[2].parse().unwrap();
                let x = e_at(&t, 3);
                let coeff: Vec<E> = (0..d).map(|i| e_at(&t, 6 + 3 * i)).collect();
                assert_eq!(
                    mle::poly_eval(&coeff, d, x),
                    e_at(&t, 6 + 3 * d),
                    "line {}",
                    lineno + 1
                );
            }
            "MLE" => {
                let k: usize = t[2].parse().unwrap();
                match t[1] {
                    "eq_table" => {
                        let z: Vec<E> = (0..k).map(|i| e_at(&t, 3 + 3 * i)).collect();
                        let mut out = vec![E::zero(); 1usize << k];
                        mle::eq_table(&z, k, &mut out);
                        for j in 0..out.len() {
                            assert_eq!(out[j], e_at(&t, 3 + 3 * k + 3 * j), "line {}", lineno + 1);
                        }
                    }
                    "eq_index" => {
                        let j: u64 = t[3].parse().unwrap(); // printed in decimal
                        let z: Vec<E> = (0..k).map(|i| e_at(&t, 4 + 3 * i)).collect();
                        assert_eq!(mle::eq_index(j, &z, k), e_at(&t, 4 + 3 * k), "line {}", lineno + 1);
                    }
                    "eq_eval" => {
                        let a: Vec<E> = (0..k).map(|i| e_at(&t, 3 + 3 * i)).collect();
                        let b: Vec<E> = (0..k).map(|i| e_at(&t, 3 + 3 * k + 3 * i)).collect();
                        assert_eq!(mle::eq_eval(&a, &b, k), e_at(&t, 3 + 6 * k), "line {}", lineno + 1);
                    }
                    "mle_eval_F" | "mle_eval_E" => {
                        let len: usize = t[3].parse().unwrap();
                        let z: Vec<E> = (0..k).map(|i| e_at(&t, 4 + 3 * i)).collect();
                        let base = 4 + 3 * k;
                        let want = e_at(&t, base + if t[1] == "mle_eval_F" { len } else { 3 * len });
                        if t[1] == "mle_eval_F" {
                            let v: Vec<F> = (0..len).map(|i| f(t[base + i])).collect();
                            assert_eq!(mle::mle_eval(&v, len, &z, k), want, "line {}", lineno + 1);
                        } else {
                            let v: Vec<E> = (0..len).map(|i| e_at(&t, base + 3 * i)).collect();
                            assert_eq!(mle::mle_eval(&v, len, &z, k), want, "line {}", lineno + 1);
                        }
                    }
                    "product_table" => {
                        let len: usize = t[3].parse().unwrap();
                        let fct: Vec<F> = (0..k).map(|i| f(t[4 + i])).collect();
                        let base = 4 + k;
                        let mut out = vec![F::zero(); len];
                        mle::product_table(&fct, k, len, &mut out);
                        for j in 0..len {
                            assert_eq!(out[j], f(t[base + j]), "line {}", lineno + 1);
                        }
                    }
                    "product_index" => {
                        let j: u64 = t[3].parse().unwrap(); // printed in decimal
                        let fct: Vec<F> = (0..k).map(|i| f(t[4 + i])).collect();
                        assert_eq!(mle::product_index(&fct, k, j), f(t[4 + k]), "line {}", lineno + 1);
                    }
                    "product_mle" => {
                        let fct: Vec<F> = (0..k).map(|i| f(t[3 + i])).collect();
                        let z: Vec<E> = (0..k).map(|i| e_at(&t, 3 + k + 3 * i)).collect();
                        assert_eq!(mle::product_mle(&fct, &z, k), e_at(&t, 3 + 4 * k), "line {}", lineno + 1);
                    }
                    "product_dot_F" | "product_dot_E" => {
                        let len: usize = t[3].parse().unwrap();
                        let fct: Vec<F> = (0..k).map(|i| f(t[4 + i])).collect();
                        let base = 4 + k;
                        if t[1] == "product_dot_F" {
                            let v: Vec<F> = (0..len).map(|i| f(t[base + i])).collect();
                            assert_eq!(
                                mle::product_dot(&v, len, &fct, k),
                                f(t[base + len]),
                                "line {}",
                                lineno + 1
                            );
                        } else {
                            let v: Vec<E> = (0..len).map(|i| e_at(&t, base + 3 * i)).collect();
                            assert_eq!(
                                mle::product_dot(&v, len, &fct, k),
                                e_at(&t, base + 3 * len),
                                "line {}",
                                lineno + 1
                            );
                        }
                    }
                    op => panic!("unknown MLE op {} at line {}", op, lineno + 1),
                }
            }
            other => panic!("unknown vector kind {} at line {}", other, lineno + 1),
        }
        lines += 1;
    }
    assert_eq!(lines, 18_256, "the fixture has 18,256 vector lines");
}
