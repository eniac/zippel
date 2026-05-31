//! Smoke tests proving the const-generic-W refactor monomorphises
//! at non-default widths. With `W=8`, `max_vars = W*8 - 1 = 63`, so
//! we can build rings with var counts that are unreachable at the
//! default `W=4` (cap 31).

use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::compute_gb;
use ark_gb::monomial::{GrevLexTerm, MonoTerm, Monomial};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

fn mono<const W: usize>(ring: &Ring<Fr, W>, exps: &[u32]) -> GrevLexTerm<W> {
    GrevLexTerm::from(MonoTerm::<W>::from_exponents(ring, exps).unwrap())
}

/// `Ring::<Fr, 8>` accepts up to 63 variables, vs. 31 at default
/// `W=4`. Construct one with 40 vars (impossible at W=4) and run
/// `compute_gb` on `[x_0 - x_39, x_0 - 1]`. The basis must collapse
/// to the unit ideal.
#[test]
fn w8_unit_ideal_with_var_index_above_31() {
    const W: usize = 8;
    let ring = Arc::new(Ring::<Fr, W>::new(40).unwrap());

    // f1 = x_0 - x_39
    let mut e1 = vec![0u32; 40];
    e1[0] = 1;
    let mut e1b = vec![0u32; 40];
    e1b[39] = 1;
    let f1 = Poly::<Fr, GrevLexTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &e1)),
            (-Fr::one(), mono(&ring, &e1b)),
        ],
    );

    // f2 = x_0 - x_39 - 1  (so f1 - f2 = 1)
    let zeros = vec![0u32; 40];
    let f2 = Poly::<Fr, GrevLexTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &e1)),
            (-Fr::one(), mono(&ring, &e1b)),
            (-Fr::one(), mono(&ring, &zeros)),
        ],
    );

    let gb = compute_gb(ring.clone(), vec![f1, f2]);
    assert_eq!(gb.len(), 1, "GB must collapse to the unit ideal");
    let terms: Vec<_> = gb[0].iter().collect();
    assert_eq!(terms.len(), 1);
    assert_eq!(terms[0].0, Fr::one());
    assert_eq!(terms[0].1.exponents(&ring), zeros);
}

/// Tiny W=8 GB matches the W=4 result on a problem that fits both:
/// `[x + y, x - y]` over `Fr[x, y]`, leading monomials `{x, y}`.
#[test]
fn w8_matches_w4_on_shared_problem() {
    const W: usize = 8;
    let ring = Arc::new(Ring::<Fr, W>::new(2).unwrap());
    let f1 = Poly::<Fr, GrevLexTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 0])),
            (Fr::one(), mono(&ring, &[0, 1])),
        ],
    );
    let f2 = Poly::<Fr, GrevLexTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 0])),
            (-Fr::one(), mono(&ring, &[0, 1])),
        ],
    );
    let gb = compute_gb(ring.clone(), vec![f1, f2]);
    assert_eq!(gb.len(), 2);
    let mut lm: Vec<Vec<u32>> = gb
        .iter()
        .map(|g| g.leading().unwrap().1.exponents(&ring))
        .collect();
    lm.sort();
    assert_eq!(lm, vec![vec![0, 1], vec![1, 0]]);
}

use ark_gb::monomial::OddElimTerm;
use std::cmp::Ordering;

/// B3: cmp_key vs M::cmp contract at W=8 over 63 vars (the
/// max for W=8). Mirrors the W=4 lib property test but
/// exercises the W-generic `OddElimTerm::cmp_key` impl beyond
/// the default width — including odd indices > 31, which can
/// only exist at W >= 5.
#[test]
fn w8_cmp_key_lex_matches_m_cmp_oddelim() {
    use ark_gb::monomial::Monomial as _;
    const W: usize = 8;
    let ring = Ring::<Fr, W>::new(63).unwrap();
    let n = 63usize;

    let mut s: u64 = 0xCAFEBABE_DEADBEEF;
    let mut step = || {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        s
    };

    let mut samples: Vec<MonoTerm<W>> = Vec::with_capacity(48);
    while samples.len() < 48 {
        let exps: Vec<u32> = (0..n).map(|_| (step() % 5) as u32).collect();
        if let Some(m) = MonoTerm::from_exponents(&ring, &exps) {
            samples.push(m);
        }
    }

    for a in &samples {
        for b in &samples {
            let m_cmp = OddElimTerm::<W>::from(*a).cmp(&OddElimTerm::<W>::from(*b));
            let (pa, ka) = OddElimTerm::<W>::cmp_key(a, &ring);
            let (pb, kb) = OddElimTerm::<W>::cmp_key(b, &ring);
            let lex = pa
                .cmp(&pb)
                .then_with(|| ka.iter().rev().cmp(kb.iter().rev()));
            assert_eq!(
                lex,
                m_cmp,
                "cmp_key lex disagrees with M::cmp at W=8 (a={:?} b={:?})",
                a.exponents(&ring),
                b.exponents(&ring)
            );
            // Silence unused-import warning.
            let _: Ordering = lex;
        }
    }
}

/// B4: a small ideal at W=8 with `OddElimTerm<8>` over 5 vars.
/// Confirms the reducer's heap path works correctly past the
/// W=4 default. The ideal `{x0 + x1, x0 - x1}` reduces to
/// `{x0, x1}` regardless of order; here we just need it to
/// terminate with 2 polynomials.
#[test]
fn w8_oddelim_small_gb_terminates() {
    const W: usize = 8;
    let ring = Arc::new(Ring::<Fr, W>::new(5).unwrap());

    let mk = |exps: &[u32]| -> OddElimTerm<W> {
        OddElimTerm::from(MonoTerm::<W>::from_exponents(&ring, exps).unwrap())
    };

    // f1 = x0 + x1 ; f2 = x0 - x1
    let f1 = Poly::<Fr, OddElimTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mk(&[1, 0, 0, 0, 0])),
            (Fr::one(), mk(&[0, 1, 0, 0, 0])),
        ],
    );
    let f2 = Poly::<Fr, OddElimTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mk(&[1, 0, 0, 0, 0])),
            (-Fr::one(), mk(&[0, 1, 0, 0, 0])),
        ],
    );

    let gb = compute_gb(ring.clone(), vec![f1, f2]);
    assert_eq!(gb.len(), 2, "expected GB of size 2, got {}", gb.len());
    let mut lm: Vec<Vec<u32>> = gb
        .iter()
        .map(|g| g.leading().unwrap().1.exponents(&ring))
        .collect();
    lm.sort();
    // Leading monomials are {x0, x1} in any order.
    assert_eq!(lm[0], vec![0, 1, 0, 0, 0]);
    assert_eq!(lm[1], vec![1, 0, 0, 0, 0]);
}
