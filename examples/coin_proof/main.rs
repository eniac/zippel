use ark_ff::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::ops::Mul;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== Coin Proof (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/coin_proof/coin_proof.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/coin_proof/coin_proof.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    let mut rng = rand::rngs::OsRng;

    let f = G1::rand(&mut rng);
    let g = G1::rand(&mut rng);
    let h = G1::rand(&mut rng);
    let h1 = G1::rand(&mut rng);
    let h2 = G1::rand(&mut rng);

    let x1 = F::rand(&mut rng);
    let x2 = F::rand(&mut rng);
    let r_y = F::rand(&mut rng);
    let sk_u = F::rand(&mut rng);

    let s = F::rand(&mut rng);
    let t = F::rand(&mut rng);
    let j = F::rand(&mut rng);

    let s_plus_j = s + j;
    let alpha = s_plus_j.inverse().unwrap();
    let t_plus_j = t + j;
    let beta = t_plus_j.inverse().unwrap();

    let r_b = F::rand(&mut rng);
    let r_c = F::rand(&mut rng);
    let r_d = F::rand(&mut rng);
    let r_beta = F::rand(&mut rng);

    let r_c_alpha = r_c * alpha;
    let r_d_beta = r_d * beta;

    let big_b = g.mul(sk_u) + h.mul(r_b);
    let big_c = g.mul(s) + h.mul(r_c);
    let big_d = g.mul(t) + h.mul(r_d);

    let big_y = h1.mul(x1) + h2.mul(x2) + f.mul(r_y);
    let big_s = g.mul(alpha) + g.mul(x1);
    let big_t = g.mul(sk_u) + g.mul(r_beta) + g.mul(x2);

    let k_sk_u = F::rand(&mut rng);
    let k_r_b = F::rand(&mut rng);
    let t_big_b = g.mul(k_sk_u) + h.mul(k_r_b);
    let ch = F::rand(&mut rng);
    let z_sk_u = k_sk_u + sk_u * ch;
    let z_r_b = k_r_b + r_b * ch;
    assert_eq!(
        g.mul(z_sk_u) + h.mul(z_r_b),
        t_big_b + big_b.mul(ch),
        "Native Sigma protocol check failed!"
    );
    println!("Native Sigma Protocol Check: ✓ OK");

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x1".to_string()), Value::Scalar(x1)),
        (Vid("x2".to_string()), Value::Scalar(x2)),
        (Vid("r_y".to_string()), Value::Scalar(r_y)),
        (Vid("sk_u".to_string()), Value::Scalar(sk_u)),
        (Vid("alpha".to_string()), Value::Scalar(alpha)),
        (Vid("beta".to_string()), Value::Scalar(beta)),
        (Vid("s".to_string()), Value::Scalar(s)),
        (Vid("t".to_string()), Value::Scalar(t)),
        (Vid("r_b".to_string()), Value::Scalar(r_b)),
        (Vid("r_c".to_string()), Value::Scalar(r_c)),
        (Vid("r_d".to_string()), Value::Scalar(r_d)),
        (Vid("r_beta".to_string()), Value::Scalar(r_beta)),
        (Vid("r_c_alpha".to_string()), Value::Scalar(r_c_alpha)),
        (Vid("r_d_beta".to_string()), Value::Scalar(r_d_beta)),
        (Vid("f".to_string()), Value::G1(f)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("h1".to_string()), Value::G1(h1)),
        (Vid("h2".to_string()), Value::G1(h2)),
        (Vid("big_y".to_string()), Value::G1(big_y)),
        (Vid("big_s".to_string()), Value::G1(big_s)),
        (Vid("big_t".to_string()), Value::G1(big_t)),
        (Vid("big_b".to_string()), Value::G1(big_b)),
        (Vid("big_c".to_string()), Value::G1(big_c)),
        (Vid("big_d".to_string()), Value::G1(big_d)),
        (Vid("j".to_string()), Value::Scalar(j)),
    ])
}
