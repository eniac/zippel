//! Cross-check Katsura / Cyclic generators against Sage's published examples.

use ark_bls12_381::Fr;
use ark_gb::monomial::{GrevLexTerm, Monomial};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

#[path = "../benches/groebner_shared.rs"]
mod shared;
use shared::{cyclic_polys, grevlex_ring, katsura_polys, var_poly};

fn grev_poly(ring: &Ring<Fr>, terms: &[(i64, &[(usize, usize)])]) -> Poly<Fr, GrevLexTerm> {
    let unit = GrevLexTerm::one(ring);
    let mut out = Poly::<Fr, GrevLexTerm>::zero();
    for (coeff, mono) in terms {
        let mag = Fr::from(coeff.unsigned_abs());
        let c = if *coeff < 0 { -mag } else { mag };
        let mut term = Poly::<Fr, GrevLexTerm>::from_terms(ring, vec![(c, unit)]);
        for &(vi, power) in *mono {
            for _ in 0..power {
                let v = var_poly::<GrevLexTerm>(ring, vi);
                term = term.mul(&v, ring);
            }
        }
        out = out.add(&term, ring);
    }
    out
}

#[test]
fn katsura_3_matches_sage() {
    let ring = grevlex_ring(3);
    let got = katsura_polys::<GrevLexTerm>(&ring);
    assert_eq!(got.len(), 3);

    let lin = grev_poly(
        &ring,
        &[(1, &[(0, 1)]), (2, &[(1, 1)]), (2, &[(2, 1)]), (-1, &[])],
    );
    let q0 = grev_poly(
        &ring,
        &[
            (1, &[(0, 2)]),
            (2, &[(1, 2)]),
            (2, &[(2, 2)]),
            (-1, &[(0, 1)]),
        ],
    );
    let q1 = grev_poly(
        &ring,
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

#[test]
fn cyclic_3_matches_sage() {
    let ring = grevlex_ring(3);
    let got = cyclic_polys::<GrevLexTerm>(&ring);
    assert_eq!(got.len(), 3);

    let deg1 = grev_poly(&ring, &[(1, &[(0, 1)]), (1, &[(1, 1)]), (1, &[(2, 1)])]);
    let deg2 = grev_poly(
        &ring,
        &[
            (1, &[(0, 1), (1, 1)]),
            (1, &[(1, 1), (2, 1)]),
            (1, &[(2, 1), (0, 1)]),
        ],
    );
    let deg3 = grev_poly(&ring, &[(1, &[(0, 1), (1, 1), (2, 1)]), (-1, &[])]);

    assert_eq!(got[0], deg1);
    assert_eq!(got[1], deg2);
    assert_eq!(got[2], deg3);
}

#[test]
fn generator_counts() {
    for n in 3..=5 {
        let ring = grevlex_ring(n);
        assert_eq!(katsura_polys::<GrevLexTerm>(&ring).len(), n);
    }
    for n in 4..=5 {
        let ring = grevlex_ring(n);
        assert_eq!(cyclic_polys::<GrevLexTerm>(&ring).len(), n);
    }
}
