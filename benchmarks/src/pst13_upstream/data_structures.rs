//! Vendored verbatim from `ark-poly-commit-0.6.0/src/multilinear_pc/data_structures.rs`.
//! No changes — these are pure data containers consumed by setup/trim/commit/open/check.

use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

#[allow(type_alias_bounds)]
pub type EvaluationHyperCubeOnG1<E: Pairing> = Vec<E::G1Affine>;
#[allow(type_alias_bounds)]
pub type EvaluationHyperCubeOnG2<E: Pairing> = Vec<E::G2Affine>;

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct UniversalParams<E: Pairing> {
    pub num_vars: usize,
    pub powers_of_g: Vec<EvaluationHyperCubeOnG1<E>>,
    pub powers_of_h: Vec<EvaluationHyperCubeOnG2<E>>,
    pub g: E::G1Affine,
    pub h: E::G2Affine,
    pub g_mask: Vec<E::G1Affine>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct CommitterKey<E: Pairing> {
    pub nv: usize,
    pub powers_of_g: Vec<EvaluationHyperCubeOnG1<E>>,
    pub powers_of_h: Vec<EvaluationHyperCubeOnG2<E>>,
    pub g: E::G1Affine,
    pub h: E::G2Affine,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct VerifierKey<E: Pairing> {
    pub nv: usize,
    pub g: E::G1Affine,
    pub h: E::G2Affine,
    pub g_mask_random: Vec<E::G1Affine>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct Commitment<E: Pairing> {
    pub nv: usize,
    pub g_product: E::G1Affine,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct Proof<E: Pairing> {
    pub proofs: Vec<E::G2Affine>,
}
