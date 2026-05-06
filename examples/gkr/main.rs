use ark_ff::{Field, Zero};
use ark_poly::DenseMultilinearExtension;
use backend::VirtualPolynomial;
use backend::poly_variant::PolyVariant;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn mle_from_vec(num_vars: usize, evals: Vec<<ArkBls12_381 as ArkConfig>::F>) -> Value<ArkBls12_381> {
    let mle = DenseMultilinearExtension::from_evaluations_vec(num_vars, evals);
    Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(mle)))
}

fn extract_vpoly(v: Value<ArkBls12_381>) -> VirtualPolynomial<<ArkBls12_381 as ArkConfig>::F> {
    if let Value::Poly(p) = v { p } else { panic!() }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    
    // Circuit:
    // L0 (size 2^1): V0[0] = V1[0] + V1[1], V0[1] = 0
    // L1 (size 2^1): V1[0] = V2[0] * V2[1], V1[1] = V2[2] * V2[3]
    // L2 (size 2^2): V2 = [1, 2, 3, 4]
    
    let v2_vals = vec![F::from(1u64), F::from(2u64), F::from(3u64), F::from(4u64)];
    let v1_vals = vec![v2_vals[0] * v2_vals[1], v2_vals[2] * v2_vals[3]]; // [2, 12]
    let v0_vals = vec![v1_vals[0] + v1_vals[1], F::zero()]; // [14, 0]
    
    let v1_mle = mle_from_vec(1, v1_vals.clone());
    let v2_mle = mle_from_vec(2, v2_vals.clone());
    
    // add_0: L0->L1. Size 1 bit for a, 1 bit for b, 1 bit for c. Total 3 bits (8 evals).
    let mut add_0_evals = vec![F::zero(); 8];
    // a=0, b=0, c=1 -> x0=0, x1=0, x2=1 -> idx=4
    add_0_evals[4] = F::from(1u64); 
    let add_0_mle = mle_from_vec(3, add_0_evals.clone());
    
    let mul_0_evals = vec![F::zero(); 8];
    let mul_0_mle = mle_from_vec(3, mul_0_evals.clone());
    
    // add_1: L1->L2. a: 1 bit, b: 2 bits, c: 2 bits. Total 5 bits (32 evals).
    let add_1_evals = vec![F::zero(); 32];
    let add_1_mle = mle_from_vec(5, add_1_evals.clone());
    
    // mul_1: L1->L2. a: 1 bit, b: 2 bits, c: 2 bits.
    let mut mul_1_evals = vec![F::zero(); 32];
    // a=0, b=0, c=1 -> x0=0, x1=0, x2=0, x3=1, x4=0 -> idx=8
    mul_1_evals[8] = F::from(1u64);
    // a=1, b=2, c=3 -> x0=1, x1=0, x2=1, x3=1, x4=1 -> 1 + 4 + 8 + 16 = 29
    mul_1_evals[29] = F::from(1u64);
    let mul_1_mle = mle_from_vec(5, mul_1_evals.clone());
    
    // Compute g_0
    let mut add_0_fixed_evals = vec![F::zero(); 4];
    // b=0, c=1 -> x0=0, x1=1 -> idx=2
    add_0_fixed_evals[2] = F::from(1u64);
    let add_0_fixed = extract_vpoly(mle_from_vec(2, add_0_fixed_evals));
    
    let mut v1_b_evals = vec![F::zero(); 4];
    v1_b_evals[0] = v1_vals[0]; v1_b_evals[1] = v1_vals[1];
    v1_b_evals[2] = v1_vals[0]; v1_b_evals[3] = v1_vals[1];
    let v1_b = extract_vpoly(mle_from_vec(2, v1_b_evals));
    
    let mut v1_c_evals = vec![F::zero(); 4];
    v1_c_evals[0] = v1_vals[0]; v1_c_evals[1] = v1_vals[0];
    v1_c_evals[2] = v1_vals[1]; v1_c_evals[3] = v1_vals[1];
    let v1_c = extract_vpoly(mle_from_vec(2, v1_c_evals));
    
    let v1_b_plus_c = v1_b.poly_add(&v1_c).unwrap();
    let g_0_vp = add_0_fixed.poly_mul(&v1_b_plus_c).unwrap();
    
    // Compute g_1
    let mut mul_1_fixed_evals = vec![F::zero(); 16];
    // b=0, c=1 -> x0=0, x1=0, x2=1, x3=0 -> idx=4
    mul_1_fixed_evals[4] = F::from(1u64);
    let mul_1_fixed = extract_vpoly(mle_from_vec(4, mul_1_fixed_evals));
    
    let mut v2_b_evals = vec![F::zero(); 16];
    let mut v2_c_evals = vec![F::zero(); 16];
    for b in 0..4 {
        for c in 0..4 {
            v2_b_evals[b + c * 4] = v2_vals[b];
            v2_c_evals[b + c * 4] = v2_vals[c];
        }
    }
    let v2_b_vp = extract_vpoly(mle_from_vec(4, v2_b_evals));
    let v2_c_vp = extract_vpoly(mle_from_vec(4, v2_c_evals));
    let v2_b_times_c = v2_b_vp.poly_mul(&v2_c_vp).unwrap();
    let g_1_vp = mul_1_fixed.poly_mul(&v2_b_times_c).unwrap();
    
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("output_point".to_string()), Value::VecScalar(vec![F::zero()])),
        (Vid("output_val".to_string()), Value::Scalar(v0_vals[0])),
        (Vid("add_0".to_string()), add_0_mle),
        (Vid("mul_0".to_string()), mul_0_mle),
        (Vid("g_0".to_string()), Value::Poly(g_0_vp)),
        (Vid("v_1_mle".to_string()), v1_mle),
        (Vid("r_1".to_string()), Value::VecScalar(vec![F::zero()])),
        (Vid("v_1".to_string()), Value::Scalar(v1_vals[0])),
        (Vid("add_1".to_string()), add_1_mle),
        (Vid("mul_1".to_string()), mul_1_mle),
        (Vid("g_1".to_string()), Value::Poly(g_1_vp)),
        (Vid("v_2_mle".to_string()), v2_mle),
    ])
}

fn main() {
    println!("=== GKR (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/gkr/gkr.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let sizes = Ctx::new();
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

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
}
