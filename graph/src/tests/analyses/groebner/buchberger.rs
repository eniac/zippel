//! Unit tests for the legacy in-tree Buchberger implementation. Production
//! code in `analyses::groebner::buchberger` dispatches through ark-gb, but the
//! test-only legacy implementation and these tests are retained as the
//! algorithmic reference. See `tests::analyses::groebner::regression` for
//! cross-backend equality.

#![cfg(test)]

use ark_bls12_381::Fr as Fp;
use ark_ff::{AdditiveGroup, One};
use backend::ATyp;
use core::cmp::Ordering;
use lang::id::Vid;
use lang::typ::{Distribution, Qualifier};
use log::debug;
use petgraph::graph::NodeIndex;
use share::assert_deq;

use crate::PRef;
use crate::analyses::groebner::buchberger::GroebnerBasis;
use crate::analyses::groebner::monomial::{ElimTerm, GrevLexTerm, Monomial};
use crate::analyses::groebner::sparsepoly::{
    SparsePolynomial, elim_sparse_poly, grevlex_sparse_poly,
};

fn elim_var(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Private,
        Distribution::Uniform,
    )
}

fn noelim_var(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Public,
        Distribution::Nonuniform,
    )
}

fn elim_term(vars: Vec<(&PRef, usize)>) -> ElimTerm {
    ElimTerm::from(
        vars.into_iter()
            .map(|(v, i)| (v.clone(), i))
            .collect::<Vec<_>>(),
    )
}

fn grevlex_term(vars: Vec<(&PRef, usize)>) -> GrevLexTerm {
    GrevLexTerm::from(
        vars.into_iter()
            .map(|(v, i)| (v.clone(), i))
            .collect::<Vec<_>>(),
    )
}

#[test]
fn test_term_ops() {
    let x = elim_var("x");
    let y = elim_var("y");
    let z = elim_var("z");

    let t1 = elim_term(vec![(&x, 2), (&y, 3)]); // x^2 y^3 (vars 0, 1)
    let t2 = elim_term(vec![(&x, 1), (&y, 2)]); // x y^2
    let t3 = elim_term(vec![(&z, 1)]); // z

    // term_mult
    let t1_t2_mult = &t1 * &t2; // x^3 y^5
    assert_deq!(t1_t2_mult, elim_term(vec![(&x, 3), (&y, 5)]));

    let t1_t3_mult = &t1 * &t3; // x^2 y^3 z
    assert_deq!(t1_t3_mult, elim_term(vec![(&x, 2), (&y, 3), (&z, 1)]));

    // term_is_divided
    assert!(t1.is_divided(&t2));
    assert!(!t2.is_divided(&t1));
    assert!(!t1.is_divided(&t3));

    // term_div
    let t1_div_t2 = (&t1 / &t2).unwrap(); // x y
    assert_deq!(t1_div_t2, elim_term(vec![(&x, 1), (&y, 1)]));
    assert!((&t2 / &t1).is_none());

    // lcm_terms
    let lcm_t1_t2 = t1.lcm(&t2); // x^2 y^3
    assert_deq!(lcm_t1_t2, t1);

    let t4 = elim_term(vec![(&x, 3), (&y, 1)]); // x^3 y
    let lcm_t1_t4 = t1.lcm(&t4); // x^3 y^3
    assert_deq!(lcm_t1_t4, elim_term(vec![(&x, 3), (&y, 3)]));
}

#[test]
fn test_s_polynomial() {
    let x = elim_var("x");
    let y = elim_var("y");

    let f: SparsePolynomial<Fp, ElimTerm> = elim_sparse_poly(vec![
        (Fp::one(), vec![(&x, 2)]),  // x^2
        (-Fp::one(), vec![(&y, 1)]), // -y
    ]); // x^2 - y

    let g = elim_sparse_poly(vec![
        (Fp::one(), vec![(&x, 1), (&y, 1)]), // xy
        (Fp::one(), vec![]),                 // +1
    ]); // xy + 1

    // LT(f) = x^2, LT(g) = xy
    // lcm(LT(f), LT(g)) = x^2 y
    // multiplier_f = (x^2 y / x^2) * (1/-1) = y
    // multiplier_g = (x^2 y / xy) * (1/1) = x
    // S(f, g) = y * (x^2 - y) - x * (xy + 1)
    //         = x^2 y - y^2 - x^2 y - x
    //         = -y^2 - x
    // Leading term (lexicographic, y < x): -x

    let s = f.s_poly(&g);

    let expected_s = elim_sparse_poly(vec![
        (-Fp::one(), vec![(&x, 1)]), // -x
        (-Fp::one(), vec![(&y, 2)]), // -y^2
    ]);

    assert_deq!(s, expected_s);
}

#[test]
fn test_grevlex_ordering() {
    let x1 = elim_var("x1");
    let x2 = elim_var("x2");
    let x3 = elim_var("x3");

    let f1 = grevlex_term(vec![(&x1, 2)]); // x1^2
    let f2 = grevlex_term(vec![(&x1, 1), (&x2, 1)]); // x1 x2
    let f4 = grevlex_term(vec![(&x2, 2)]); // x2^2
    let f3 = grevlex_term(vec![(&x1, 1), (&x3, 1)]); // x1 x3
    let f5 = grevlex_term(vec![(&x2, 1), (&x3, 1)]); // x2 x3
    let f6 = grevlex_term(vec![(&x3, 2)]); // x3^2
    let f7 = grevlex_term(vec![]); // 1

    // Textbook degrevlex with variable ordering x1 > x2 > x3 (i.e. x3 is the
    // "rightmost" / smallest variable). Largest monomial first, then tied on
    // degree => smallest exponent on x3, then x2. Leading (= largest) sorts
    // FIRST under this `Ord` (see `leading_term` / `BTreeMap::first`):
    //   x1^2  >  x1*x2  >  x2^2  >  x1*x3  >  x2*x3  >  x3^2  >  1
    let mut terms = vec![&f3, &f4, &f1, &f5, &f6, &f2, &f7]
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();

    terms.sort_unstable();
    assert_eq!(terms, vec![f1, f2, f4, f3, f5, f6, f7]);
}

/// Textbook degrevlex counterexamples that caught the old left-to-right
/// tie-breaker. With PRef ordering x1 < x2 < x3, "rightmost" = x3.
/// Under "leading = Ord::Less" convention: the larger monomial returns `Less`.
#[test]
fn test_grevlex_degrevlex_counterexamples() {
    let x1 = elim_var("x1");
    let x2 = elim_var("x2");
    let x3 = elim_var("x3");

    // x1^2 vs x2*x3 (both deg 2). Rightmost differing var is x3: x1^2 has
    // exp 0, x2*x3 has exp 1. Larger exp on x3 => smaller monomial; so
    // x1^2 > x2*x3, i.e. x1^2 is leading => Ord::Less.
    let a = grevlex_term(vec![(&x1, 2)]);
    let b = grevlex_term(vec![(&x2, 1), (&x3, 1)]);
    assert_eq!(a.cmp(&b), Ordering::Less, "x1^2 > x2*x3 in degrevlex");

    // x1^2 vs x1*x2. Rightmost differing is x2: x1^2 has 0, x1*x2 has 1.
    // x1^2 leading => Ord::Less.
    let a = grevlex_term(vec![(&x1, 2)]);
    let b = grevlex_term(vec![(&x1, 1), (&x2, 1)]);
    assert_eq!(a.cmp(&b), Ordering::Less, "x1^2 > x1*x2 in degrevlex");

    // x2^2 vs x1*x3. Both deg 2. Rightmost differing is x3: x2^2 has 0,
    // x1*x3 has 1. x2^2 leading => Ord::Less. (This specifically distinguishes
    // degrevlex from graded-lex, which would say x1*x3 > x2^2.)
    let a = grevlex_term(vec![(&x2, 2)]);
    let b = grevlex_term(vec![(&x1, 1), (&x3, 1)]);
    assert_eq!(a.cmp(&b), Ordering::Less, "x2^2 > x1*x3 in degrevlex");

    // Degree dominates: x1 (deg 1) < x3^2 (deg 2) in "leading" sense means
    // x3^2 leading => x3^2.cmp(x1) = Less.
    let a = grevlex_term(vec![(&x3, 2)]);
    let b = grevlex_term(vec![(&x1, 1)]);
    assert_eq!(a.cmp(&b), Ordering::Less, "higher degree is leading");
}

/// Regression test: `PartialOrd` and `Ord` impls must agree on `ElimTerm` and
/// `GrevLexTerm`. This is exactly what `clippy::derive_ord_xor_partial_ord`
/// guards. If anyone re-derives `PartialOrd` (auto field-by-field tuple order)
/// without re-checking it matches the manual `Ord`, this test catches it.
#[test]
fn test_partial_ord_agrees_with_ord() {
    let x1 = elim_var("x1");
    let x2 = elim_var("x2");
    let x3 = elim_var("x3");

    let elim_terms: Vec<ElimTerm> = vec![
        elim_term(vec![]),                             // 1
        elim_term(vec![(&x1, 2)]),                     // x1^2
        elim_term(vec![(&x1, 1), (&x2, 1)]),           // x1 x2
        elim_term(vec![(&x2, 2)]),                     // x2^2
        elim_term(vec![(&x1, 1), (&x3, 1)]),           // x1 x3
        elim_term(vec![(&x2, 1), (&x3, 1)]),           // x2 x3
        elim_term(vec![(&x3, 2)]),                     // x3^2
        elim_term(vec![(&x1, 3)]),                     // x1^3
        elim_term(vec![(&x1, 1), (&x2, 1), (&x3, 1)]), // x1 x2 x3
    ];

    for a in &elim_terms {
        for b in &elim_terms {
            assert_eq!(
                a.partial_cmp(b),
                Some(a.cmp(b)),
                "ElimTerm: PartialOrd and Ord disagree on ({a:?}, {b:?})"
            );
        }
    }

    let grevlex_terms: Vec<GrevLexTerm> = vec![
        grevlex_term(vec![]),
        grevlex_term(vec![(&x1, 2)]),
        grevlex_term(vec![(&x1, 1), (&x2, 1)]),
        grevlex_term(vec![(&x2, 2)]),
        grevlex_term(vec![(&x1, 1), (&x3, 1)]),
        grevlex_term(vec![(&x2, 1), (&x3, 1)]),
        grevlex_term(vec![(&x3, 2)]),
        grevlex_term(vec![(&x1, 3)]),
        grevlex_term(vec![(&x1, 1), (&x2, 1), (&x3, 1)]),
    ];

    for a in &grevlex_terms {
        for b in &grevlex_terms {
            assert_eq!(
                a.partial_cmp(b),
                Some(a.cmp(b)),
                "GrevLexTerm: PartialOrd and Ord disagree on ({a:?}, {b:?})"
            );
        }
    }
}

// A simple test case for a linear system, this should work as Gaussian elimination
#[test]
fn test_linear() {
    let a = elim_var("a");
    let b = elim_var("b");
    let s1 = elim_var("s1");
    let s2 = elim_var("s2");
    let r = elim_var("r");
    let num_vars = 5;

    // s1 + r - a
    let f1: SparsePolynomial<Fp, GrevLexTerm> = grevlex_sparse_poly(vec![
        (-Fp::one(), vec![(&a, 1)]), // -a
        (Fp::one(), vec![(&s1, 1)]), // s1
        (Fp::one(), vec![(&r, 1)]),  // r
    ]);

    // s2 + r - b
    let f2 = grevlex_sparse_poly(vec![
        (-Fp::one(), vec![(&b, 1)]), // -b
        (Fp::one(), vec![(&s2, 1)]), // s2
        (Fp::one(), vec![(&r, 1)]),  // r
    ]);

    let initial_basis = GroebnerBasis::new(num_vars, vec![f1, f2]);
    debug!("Ideal:");
    for p in initial_basis.iter() {
        debug!("{}", p);
    }

    let groebner_basis = initial_basis.buchberger::<8>();
    debug!("Computed Gröbner Basis:");
    for p in groebner_basis.iter() {
        debug!("{}", p);
    }
}

// A simple test case from the Maplesoft docs for Groebner LexDeg bases
#[test]
fn test_maple() {
    let t = elim_var("t");
    let x = noelim_var("x");
    let y = noelim_var("y");
    let num_vars = 3;

    // Ideal
    let f1: SparsePolynomial<Fp, ElimTerm> = elim_sparse_poly(vec![
        (Fp::one(), vec![(&t, 2), (&y, 1)]),  // t^2 y
        (-Fp::one().double(), vec![(&t, 1)]), // -2t
        (Fp::one(), vec![(&y, 1)]),           // +y
    ]);

    let f2 = elim_sparse_poly(vec![
        (Fp::one(), vec![(&t, 2), (&x, 1)]), // t^2 x
        (Fp::one(), vec![(&t, 2)]),          // t^2
        (Fp::one(), vec![(&x, 1)]),          // x
        (-Fp::one(), vec![]),                // -1
    ]);

    let initial_basis = GroebnerBasis::new(num_vars, vec![f1, f2]);
    let groebner_basis = initial_basis.buchberger_and_reduce::<8>();

    // The correct result should be:
    // t*x + t - y
    // t*y + x - 1
    // x^2 + y^2 - 1
    let g1 = elim_sparse_poly(vec![
        (Fp::one(), vec![(&t, 1), (&x, 1)]), // tx
        (Fp::one(), vec![(&t, 1)]),          // t
        (-Fp::one(), vec![(&y, 1)]),         // -y
    ]);

    let g2 = elim_sparse_poly(vec![
        (Fp::one(), vec![(&t, 1), (&y, 1)]), // ty
        (Fp::one(), vec![(&x, 1)]),          // x
        (-Fp::one(), vec![]),                // -1
    ]);

    let g3 = elim_sparse_poly(vec![
        (Fp::one(), vec![(&x, 2)]), // x^2
        (Fp::one(), vec![(&y, 2)]), // y^2
        (-Fp::one(), vec![]),       // -1
    ]);

    assert_eq!(
        groebner_basis,
        GroebnerBasis::new(num_vars, vec![g1, g2, g3])
    );
}
