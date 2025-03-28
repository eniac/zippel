use ark_ff::UniformRand;
use rand::Rng;
use core::hash::Hasher;
use rayon::prelude::*;

use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldValue<F: ark_ff::FftField> {
    Field(F),
    Vec(Vec<F>, usize),
    Uni(Uni<F>),
    Mle(Mle<F>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GroupValue<G: ark_ff::AdditiveGroup> {
    Group(G),
    Vec(Vec<G>, usize),
}

pub enum ValueType {
    G1,
    G2,
    GT,
    F2,
    F
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    Bls12381(ark_bls12_381::Fr),
    Bls12377(ark_bls12_377::Fr),
    EdOnCp6_782(ark_ed_on_cp6_782::Fr),
    Bn254(ark_bn254::Fr),
    MNT4_298(ark_mnt4_298::Fr),
    MNT4_753(ark_mnt4_753::Fr),
    Pallas(ark_pallas::Fr),
    Secp256k1(ark_secp256k1::Fr),
    Curve25519(ark_curve25519::Fr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Group {
    Bls12377G1,
    Bls12377G2,
    Bls12377Gt,
    Bls12381G1,
    Bls12381G2,
    EdOnCp6_782,
    Bn254G1,
    Bn254G2,
    MNT4_298G1,
    MNT4_298G2,
    MNT4_753G1,
    MNT4_753G2,
    Pallas,
    Vesta,
    Secp256k1,
    Curve25519,
}

