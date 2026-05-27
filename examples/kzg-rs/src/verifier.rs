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

#[allow(clippy::too_many_arguments)]
pub async fn verify(
    eval_point: ark_bls12_381::Fr,
    eval_result: ark_bls12_381::Fr,
    gen_g1: ark_bls12_381::G1Projective,
    gen_g2: ark_bls12_381::G2Projective,
    srs_g1: Vec<ark_bls12_381::G1Projective>,
    srs_g2_s: ark_bls12_381::G2Projective,
    proof: &crate::prover::Proof,
) -> Result<bool, GeneratedError> {
    let proof_element = proof.proof.clone();
    let commitment = proof.commitment.clone();
    let left_srs_g2_s = srs_g2_s.clone();
    let left_gen_g2 = gen_g2.clone();
    let left_eval_point = eval_point.clone();

    let left_handle = tokio::spawn(async move {
        let pairing_lhs = pair(proof_element, left_srs_g2_s - left_gen_g2 * left_eval_point);
        Ok::<_, GeneratedError>(pairing_lhs)
    });
    let right_handle = tokio::spawn(async move {
        let pairing_rhs = pair(commitment - gen_g1 * eval_result, gen_g2);
        Ok::<_, GeneratedError>(pairing_rhs)
    });

    let pairing_lhs = left_handle.await??;
    let pairing_rhs = right_handle.await??;
    Ok(pairing_lhs == pairing_rhs)
}
