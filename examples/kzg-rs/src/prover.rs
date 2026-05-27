#![allow(dead_code, unused_imports, unused_variables)]

use ark_ec::pairing::Pairing;
use ark_std::Zero;

#[derive(Debug)]
pub enum GeneratedError {
    Join(tokio::task::JoinError),
    LengthMismatch {
        context: &'static str,
        left: usize,
        right: usize,
    },
    EmptyPolynomial,
}

impl From<tokio::task::JoinError> for GeneratedError {
    fn from(value: tokio::task::JoinError) -> Self {
        Self::Join(value)
    }
}

impl std::fmt::Display for GeneratedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Join(err) => write!(f, "tokio task join error: {err}"),
            Self::LengthMismatch {
                context,
                left,
                right,
            } => {
                write!(f, "{context} length mismatch: {left} != {right}")
            }
            Self::EmptyPolynomial => write!(f, "polynomial must contain at least one coefficient"),
        }
    }
}

impl std::error::Error for GeneratedError {}

fn msm_g1(
    scalars: &[ark_bls12_381::Fr],
    bases: &[ark_bls12_381::G1Projective],
) -> Result<ark_bls12_381::G1Projective, GeneratedError> {
    if scalars.len() != bases.len() {
        return Err(GeneratedError::LengthMismatch {
            context: "G1 MSM",
            left: scalars.len(),
            right: bases.len(),
        });
    }

    Ok(scalars.iter().zip(bases).fold(
        ark_bls12_381::G1Projective::zero(),
        |acc, (scalar, base)| acc + *base * *scalar,
    ))
}

fn quotient_by_linear(
    poly_coeffs: &[ark_bls12_381::Fr],
    point: ark_bls12_381::Fr,
    value: ark_bls12_381::Fr,
) -> Result<Vec<ark_bls12_381::Fr>, GeneratedError> {
    if poly_coeffs.is_empty() {
        return Err(GeneratedError::EmptyPolynomial);
    }
    if poly_coeffs.len() == 1 {
        return Ok(Vec::new());
    }

    let mut dividend = poly_coeffs.to_vec();
    dividend[0] -= value;

    let degree = dividend.len() - 1;
    let mut quotient = vec![ark_bls12_381::Fr::zero(); degree];
    quotient[degree - 1] = dividend[degree];
    for i in (1..degree).rev() {
        quotient[i - 1] = dividend[i] + point * quotient[i];
    }
    Ok(quotient)
}

fn pair(
    g1: ark_bls12_381::G1Projective,
    g2: ark_bls12_381::G2Projective,
) -> ark_ec::pairing::PairingOutput<ark_bls12_381::Bls12_381> {
    ark_bls12_381::Bls12_381::pairing(g1, g2)
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub commitment: ark_bls12_381::G1Projective,
    pub proof: ark_bls12_381::G1Projective,
}

#[allow(clippy::too_many_arguments)]
pub async fn prove(
    eval_point: ark_bls12_381::Fr,
    eval_result: ark_bls12_381::Fr,
    gen_g1: ark_bls12_381::G1Projective,
    gen_g2: ark_bls12_381::G2Projective,
    poly_coeffs: Vec<ark_bls12_381::Fr>,
    srs_g1: Vec<ark_bls12_381::G1Projective>,
    srs_g2_s: ark_bls12_381::G2Projective,
) -> Result<Proof, GeneratedError> {
    let commitment_scalars = poly_coeffs.clone();
    let commitment_bases = srs_g1.clone();
    let commitment_handle =
        tokio::spawn(async move { msm_g1(&commitment_scalars, &commitment_bases) });

    let quotient_coeffs = quotient_by_linear(&poly_coeffs, eval_point, eval_result)?;
    let srs_g1_truncated: Vec<_> = srs_g1.into_iter().take(quotient_coeffs.len()).collect();
    let proof_handle = tokio::spawn(async move { msm_g1(&quotient_coeffs, &srs_g1_truncated) });

    let commitment = commitment_handle.await??;
    let proof = proof_handle.await??;
    Ok(Proof { commitment, proof })
}
