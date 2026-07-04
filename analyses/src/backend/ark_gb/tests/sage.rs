//! Cross-check the ported Katsura / Cyclic generators against Sage's
//! published `sage.rings.ideal.Katsura` / `sage.rings.ideal.Cyclic`
//! small-n examples.

use crate::PRef;
use crate::frontend::Polynomial;
use ark_bls12_381::Fr;

use super::shared::{cyclic_polys, katsura_polys, mk_vars};

/// Build a polynomial from `(coeff, [(var_index, power), ...])` terms.
fn build_poly(vars: &[PRef], terms: &[(i64, &[(usize, usize)])]) -> Polynomial<Fr> {
    let mut out = Polynomial::<Fr>::zero();
    for (coeff, mono) in terms {
        let mag = Fr::from(coeff.unsigned_abs());
        let c = if *coeff < 0 { -mag } else { mag };
        let mut term = Polynomial::<Fr>::lit(&c);
        for &(vi, power) in *mono {
            let mut v = Polynomial::<Fr>::var(&vars[vi]);
            v.pow(power);
            term *= v;
        }
        out += term;
    }
    out
}

/// Sage `Katsura(P, 3)` with `P = (x, y, z)`:
///   `(x + 2y + 2z - 1, x² + 2y² + 2z² - x, 2xy + 2yz - y)`
#[test]
fn katsura_3_matches_sage() {
    let vars = mk_vars("k", 3);
    let got = katsura_polys(&vars);
    assert_eq!(got.len(), 3);

    let lin = build_poly(
        &vars,
        &[(1, &[(0, 1)]), (2, &[(1, 1)]), (2, &[(2, 1)]), (-1, &[])],
    );
    let q0 = build_poly(
        &vars,
        &[
            (1, &[(0, 2)]),
            (2, &[(1, 2)]),
            (2, &[(2, 2)]),
            (-1, &[(0, 1)]),
        ],
    );
    let q1 = build_poly(
        &vars,
        &[
            (2, &[(0, 1), (1, 1)]),
            (2, &[(1, 1), (2, 1)]),
            (-1, &[(1, 1)]),
        ],
    );

    assert_eq!(got[0], lin);
    assert_eq!(got[1], q0);
    assert_eq!(got[2], q1);
}

/// Sage `Cyclic(P, 3)` with `P = (x, y, z)`:
///   `(x + y + z, xy + xz + yz, xyz - 1)`
#[test]
fn cyclic_3_matches_sage() {
    let vars = mk_vars("c", 3);
    let got = cyclic_polys(&vars);
    assert_eq!(got.len(), 3);

    let deg1 = build_poly(&vars, &[(1, &[(0, 1)]), (1, &[(1, 1)]), (1, &[(2, 1)])]);
    let deg2 = build_poly(
        &vars,
        &[
            (1, &[(0, 1), (1, 1)]),
            (1, &[(1, 1), (2, 1)]),
            (1, &[(2, 1), (0, 1)]),
        ],
    );
    let deg3 = build_poly(&vars, &[(1, &[(0, 1), (1, 1), (2, 1)]), (-1, &[])]);

    assert_eq!(got[0], deg1);
    assert_eq!(got[1], deg2);
    assert_eq!(got[2], deg3);
}

/// Smoke test: generators produce `n` polynomials for `n` variables.
#[test]
fn generator_counts() {
    for n in 3..=5 {
        let vars = mk_vars("k", n);
        assert_eq!(katsura_polys(&vars).len(), n);
    }
    for n in 4..=5 {
        let vars = mk_vars("c", n);
        assert_eq!(cyclic_polys(&vars).len(), n);
    }
}
