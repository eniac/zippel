mod prover;
mod verifier;

use ark_bls12_381::{Fr, G1Projective, G2Projective};
use ark_std::UniformRand;

fn eval_poly(coeffs: &[Fr], point: Fr) -> Fr {
    coeffs
        .iter()
        .rev()
        .fold(Fr::from(0_u64), |acc, coeff| acc * point + coeff)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut rng = rand::rngs::OsRng;
    let poly_coeffs = vec![Fr::rand(&mut rng), Fr::rand(&mut rng)];
    let eval_point = Fr::rand(&mut rng);
    let eval_result = eval_poly(&poly_coeffs, eval_point);
    let tau = Fr::rand(&mut rng);
    let gen_g1 = G1Projective::rand(&mut rng);
    let gen_g2 = G2Projective::rand(&mut rng);
    let srs_g1 = vec![gen_g1, gen_g1 * tau];
    let srs_g2_s = gen_g2 * tau;

    let proof = prover::prove(
        eval_point,
        eval_result,
        gen_g1,
        gen_g2,
        poly_coeffs,
        srs_g1.clone(),
        srs_g2_s,
    )
    .await?;

    let passed = verifier::verify(
        eval_point,
        eval_result,
        gen_g1,
        gen_g2,
        srs_g1,
        srs_g2_s,
        &proof,
    )
    .await?;

    println!(
        "Verification:   {}",
        if passed { "PASSED" } else { "FAILED" }
    );
    if !passed {
        std::process::exit(1);
    }

    Ok(())
}
