use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use ark_std::UniformRand;
use ark_std::One;

// N = number of variables; 2^N = number of polynomial coefficients.
// To test with a different N, change N_VARS, update the inputs accordingly,
// and change `N: 2` to the desired value in pst13.zippel.
const N_VARS: usize = 2;

fn main() {
    println!("=== PST13 Multilinear PCS (ArkBls12_381, N={N_VARS}) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!("Proof size:     {proof_bytes} bytes ({} elements)", proof.len());

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
    });
    let analysis_elapsed = analysis_start.elapsed();
    match analysis_result {
        Ok(analysis) => {
            match &analysis.completeness {
                Ok(()) => println!("Completeness:   ✓"),
                Err(e) => println!("Completeness:   ✗ {}", e),
            }
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
        }
        Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    }
    println!("Analysis time:  {analysis_elapsed:.2?}");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n = N_VARS;
    let size = 1usize << n; // 2^N

    // Sample generators G (G1) and H (G2)
    let gen_g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let gen_h = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);

    // PST.Setup: sample secret trapdoor alpha = (alpha_1, ..., alpha_N)
    let one = <ArkBls12_381 as ArkConfig>::F::one();
    let alpha: Vec<_> = (0..n).map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng)).collect();
    let one_m_alpha: Vec<_> = alpha.iter().map(|a| one - a).collect();

    // PST.Setup: compute ck_N = [eq_N(alpha, i) * G  for i in {0,1}^N]
    // Index i encodes the bit-string (i_{N-1}, ..., i_1, i_0) in MSB-first order
    // so that the streaming algorithm's split-by-first-variable is a contiguous split.
    let ck_n_scalars: Vec<_> = (0..size).map(|i| {
        // Bit j (MSB = variable 1) of i
        (0..n).fold(one, |acc, j| {
            let bit = (i >> (n - 1 - j)) & 1;
            if bit == 1 { acc * alpha[j] } else { acc * one_m_alpha[j] }
        })
    }).collect();
    let ck_n = Value::VecG1(ck_n_scalars.iter().map(|s| gen_g * s).collect());

    // Sample random polynomial p = [p_{i_1...i_N} for i in {0,1}^N]
    let p_scalars: Vec<_> = (0..size).map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng)).collect();
    let p = Value::VecScalar(p_scalars.clone());

    // Sample evaluation point z = (z_1, ..., z_N)
    let z_scalars: Vec<_> = (0..n).map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng)).collect();
    let z = Value::VecScalar(z_scalars.clone());

    // Compute y = p(z) as a multilinear extension evaluation:
    //   y = sum_{i in {0,1}^N} p_i * eq_N(z, i)
    let y_val = (0..size).fold(<ArkBls12_381 as ArkConfig>::F::from(0u64), |acc, i| {
        let eq_z_i = (0..n).fold(one, |prod, j| {
            let bit = (i >> (n - 1 - j)) & 1;
            let one_m_zj = one - z_scalars[j];
            if bit == 1 { prod * z_scalars[j] } else { prod * one_m_zj }
        });
        acc + p_scalars[i] * eq_z_i
    });
    let y = Value::Scalar(y_val);

    // Compute commitment C_p = dot(p, ck_N) = p(alpha) * G
    let c_p_scalar = (0..size).fold(<ArkBls12_381 as ArkConfig>::F::from(0u64), |acc, i| {
        acc + p_scalars[i] * ck_n_scalars[i]
    });
    let c_p = Value::G1(gen_g * c_p_scalar);

    // Compute verification key: alpha_H = [alpha_i * H  for i in 1..N]
    let alpha_h = Value::VecG2(alpha.iter().map(|a| gen_h * a).collect());

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()),        p),
        (Vid("z".to_string()),        z),
        (Vid("y".to_string()),        y),
        (Vid("c_p".to_string()),      c_p),
        (Vid("ck_N".to_string()),     ck_n),
        (Vid("g_gen".to_string()),    Value::G1(gen_g)),
        (Vid("h_gen".to_string()),    Value::G2(gen_h)),
        (Vid("alpha_H".to_string()),  alpha_h),
    ])
}
