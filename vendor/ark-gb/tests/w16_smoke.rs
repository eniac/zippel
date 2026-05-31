//! Confirms `Ring::<Fr, 16>` monomorphises and runs at all. With
//! `W=16` the cap is `W*8 - 1 = 127` variables. We deliberately pick
//! a tiny problem so this test stays cheap.

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

#[test]
fn w16_tiny_problem_compiles_and_runs() {
    const W: usize = 16;
    // Use 80 vars: above the W=8 cap (63), well below W=16's 127.
    let ring = Arc::new(Ring::<Fr, W>::new(80).unwrap());

    // f1 = x_0 - 1
    let mut e0 = vec![0u32; 80];
    e0[0] = 1;
    let zeros = vec![0u32; 80];
    let f1 = Poly::<Fr, GrevLexTerm<W>, W>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &e0)),
            (-Fr::one(), mono(&ring, &zeros)),
        ],
    );

    let gb = compute_gb(ring.clone(), vec![f1]);
    assert_eq!(gb.len(), 1);
    let terms: Vec<_> = gb[0].iter().collect();
    // Already monic, already a GB: x_0 - 1.
    assert_eq!(terms.len(), 2);
    assert_eq!(terms[0].1.exponents(&ring), e0);
    assert_eq!(terms[1].1.exponents(&ring), zeros);
}
