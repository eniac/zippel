use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{
    DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, univariate::DensePolynomial,
};
use ark_std::test_rng;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;
type G1 = <C as ArkConfig>::G1;
type G2 = <C as ArkConfig>::G2;

fn main() {
    println!("=== DeKART Range Proof ===");
    let n_size = 3;
    let b_size = 2;
    let l_chunk = 8;
    let h_deg = (b_size - 1) * n_size;

    let args = ZippelArgs::new(PathBuf::from("examples/dekart/dekart.zippel"));
    let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("n"), &n_size);
    sizes.insert(&Tid::new("b"), &b_size);
    sizes.insert(&Tid::new("l_chunk"), &l_chunk);
    sizes.insert(&Tid::new("h_deg"), &h_deg);
    handler.compile(&sizes);

    let (inputs, public_inputs) = build_inputs(n_size, b_size, l_chunk, h_deg);

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<C>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let args = ZippelArgs::new(PathBuf::from("examples/dekart/dekart.zippel"));
    let mut verifier_handler: ZippelHandler<C> = ZippelHandler::new(args);
    verifier_handler.compile(&sizes);
    verifier_handler.set_public_inputs(public_inputs);
    let verifier_scheduled = verifier_handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler
        .run_verifier(verifier_scheduled, proof.clone())
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result.clone());
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        for (i, v) in verifier_result.iter().enumerate() {
            println!("  verify[{i}] = {:?}", v);
        }
        std::process::exit(1);
    }
}

fn build_inputs(
    n_size: usize,
    b_size: usize,
    l_chunk: usize,
    h_deg: usize,
) -> (Ctx<Vid, Value<C>>, Ctx<Vid, Value<C>>) {
    let mut rng = test_rng();

    // 1. Setup generators & trapdoors
    let gen_g1 = G1::rand(&mut rng);
    let gen_g2 = G2::rand(&mut rng);
    let tau = F::rand(&mut rng);
    let xi = F::rand(&mut rng);

    let srs_g2_tau = gen_g2 * tau;
    let srs_g2_xi = gen_g2 * xi;
    let xi_g1 = gen_g1 * xi;

    // 2. Monomial SRS in G1
    let mut srs_g1_n_vec = Vec::new();
    let mut current_tau = F::one();
    for _ in 0..=n_size {
        srs_g1_n_vec.push(gen_g1 * current_tau);
        current_tau *= tau;
    }

    let mut srs_g1_h_vec = Vec::new();
    current_tau = F::one();
    for _ in 0..=h_deg {
        srs_g1_h_vec.push(gen_g1 * current_tau);
        current_tau *= tau;
    }

    // 3. Witness values to prove (must be in [0, b_size^l_chunk - 1])
    // With n = n_size, b = b_size, l_chunk = l_chunk, values must be in [0, b_size^l_chunk - 1]
    let z_vals = vec![5u64, 12u64, 7u64];
    assert_eq!(z_vals.len(), n_size, "z_vals length must equal n_size");
    for &z in &z_vals {
        assert!(
            z < (b_size as u64).pow(l_chunk as u32),
            "witness value {} exceeds max allowed range {}",
            z,
            (b_size as u64).pow(l_chunk as u32) - 1
        );
    }
    let mut f_evals = vec![F::zero()];
    for z in &z_vals {
        f_evals.push(F::from(*z));
    }

    // Decompose values into radix-b digits (the prover blinds f_j(ω^0) itself)
    let mut chunks_bits = Vec::new();
    for j in 0..l_chunk {
        let digits = z_vals
            .iter()
            .map(|z| F::from((z / (b_size as u64).pow(j as u32)) % (b_size as u64)))
            .collect();
        chunks_bits.push(Value::VecScalar(digits));
    }

    // Commitment randomness of the statement
    let rho = F::rand(&mut rng);

    // Range constants
    let mut b_vals = Vec::new();
    for i in 0..b_size {
        b_vals.push(F::from(i as u64));
    }

    let mut b_pow = Vec::new();
    let mut current_pow = F::one();
    let b_scalar = F::from(b_size as u64);
    for _ in 0..l_chunk {
        b_pow.push(current_pow);
        current_pow *= b_scalar;
    }

    // 4. Compute s0_commit
    // Lagrange polynomial s0 has evaluations [1, 0, 0, 0] on the domain of size n+1
    let domain_s = GeneralEvaluationDomain::<F>::new(n_size + 1).unwrap();
    let mut s0_evals = vec![F::zero(); n_size + 1];
    s0_evals[0] = F::one();
    let s0_coeffs = domain_s.ifft(&s0_evals);
    let s0_poly = DensePolynomial::from_coefficients_vec(s0_coeffs);

    let mut s0_commit = G1::zero();
    for (coeff, g) in s0_poly.coeffs.iter().zip(srs_g1_n_vec.iter()) {
        s0_commit += *g * *coeff;
    }

    // Lagrange-basis SRS [ℓ_i(τ)]_1: ℓ_i(τ) = ifft(1, τ, ..., τ^n)_i over the same domain
    let tau_pows: Vec<F> = (0..=n_size).map(|i| tau.pow([i as u64])).collect();
    let srs_g1_lagr_vec: Vec<G1> = domain_s.ifft(&tau_pows).iter().map(|c| gen_g1 * c).collect();
    assert_eq!(srs_g1_lagr_vec[0], s0_commit);

    // 5. Statement: com_f = [f(τ)]_1 + ξ·ρ
    let f_coeffs = domain_s.ifft(&f_evals);
    let mut com_f = xi_g1 * rho;
    for (coeff, g) in f_coeffs.iter().zip(srs_g1_n_vec.iter()) {
        com_f += *g * *coeff;
    }

    let inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("f_evals".to_string()), Value::VecScalar(f_evals)),
        (Vid("chunks_bits".to_string()), Value::Vec(chunks_bits)),
        (Vid("rho".to_string()), Value::Scalar(rho)),
        (Vid("com_f".to_string()), Value::G1(com_f)),
        (Vid("b_vals".to_string()), Value::VecScalar(b_vals.clone())),
        (Vid("b_pow".to_string()), Value::VecScalar(b_pow.clone())),
        (Vid("f_one".to_string()), Value::Scalar(F::one())),
        (Vid("gen_g1".to_string()), Value::G1(gen_g1)),
        (Vid("gen_g2".to_string()), Value::G2(gen_g2)),
        (Vid("srs_g2_tau".to_string()), Value::G2(srs_g2_tau)),
        (Vid("srs_g2_xi".to_string()), Value::G2(srs_g2_xi)),
        (Vid("xi_g1".to_string()), Value::G1(xi_g1)),
        (Vid("s0_commit".to_string()), Value::G1(s0_commit)),
        (Vid("srs_g1_lagr".to_string()), Value::VecG1(srs_g1_lagr_vec)),
        (Vid("srs_g1_h".to_string()), Value::VecG1(srs_g1_h_vec)),
        (Vid("v_star".to_string()), Value::VecScalar(vec![F::one(); n_size + 1])),
    ]);

    let public_inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("com_f".to_string()), Value::G1(com_f)),
        (Vid("b_vals".to_string()), Value::VecScalar(b_vals)),
        (Vid("b_pow".to_string()), Value::VecScalar(b_pow)),
        (Vid("f_one".to_string()), Value::Scalar(F::one())),
        (Vid("gen_g1".to_string()), Value::G1(gen_g1)),
        (Vid("gen_g2".to_string()), Value::G2(gen_g2)),
        (Vid("srs_g2_tau".to_string()), Value::G2(srs_g2_tau)),
        (Vid("srs_g2_xi".to_string()), Value::G2(srs_g2_xi)),
        (Vid("xi_g1".to_string()), Value::G1(xi_g1)),
        (Vid("s0_commit".to_string()), Value::G1(s0_commit)),
    ]);

    (inputs, public_inputs)
}
