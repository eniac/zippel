mod prover;
mod verifier;

use ark_bls12_381::{Fr, G1Projective};
use ark_std::UniformRand;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut rng = rand::rngs::OsRng;
    let x = Fr::rand(&mut rng);
    let g = G1Projective::rand(&mut rng);
    let h = g * x;

    let proof = prover::prove(g.clone(), h.clone(), x).await?;
    let passed = verifier::verify(g, h, &proof).await?;

    println!(
        "Verification:   {}",
        if passed { "PASSED" } else { "FAILED" }
    );
    if !passed {
        std::process::exit(1);
    }

    Ok(())
}
