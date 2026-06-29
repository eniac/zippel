use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

const N: usize = 2;
const K: usize = 1;

fn main() {
    println!("=== CDS Protocol for Proofs of Partial Knowledge (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/cds/cds.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/cds/cds.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    let mut rng = rand::rngs::OsRng;

    let g = G1::rand(&mut rng);

    let mut w_vec = Vec::with_capacity(N);
    let mut r_vec = Vec::with_capacity(N);
    let mut b_vec = Vec::with_capacity(N);
    let mut c_sim_vec = Vec::with_capacity(N);
    let mut m2_sim_vec = Vec::with_capacity(N);
    let mut pk_vec = Vec::with_capacity(N);

    let mut u_points_vec = Vec::new();
    let mut u_evals_vec = Vec::new();
    let mut eval_points_vec = Vec::with_capacity(N);

    for i in 0..N {
        let is_known = i < (N - K);
        eval_points_vec.push(F::from((i + 1) as u64));

        let w_val = F::rand(&mut rng);
        w_vec.push(w_val);

        let pk_affines = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &[w_val]);
        let pk = pk_affines.into_iter().next().unwrap();
        pk_vec.push(pk);

        let r_val = F::rand(&mut rng);
        r_vec.push(r_val);

        let c_sim_val = F::rand(&mut rng);
        c_sim_vec.push(c_sim_val);

        let m2_sim_val = F::rand(&mut rng);
        m2_sim_vec.push(m2_sim_val);

        if is_known {
            b_vec.push(F::from(1u64));
        } else {
            b_vec.push(F::from(0u64));
            u_points_vec.push(F::from((i + 1) as u64));
            u_evals_vec.push(c_sim_val);
        }
    }

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("public_keys".to_string()), Value::VecG1Affine(pk_vec)),
        (
            Vid("eval_points".to_string()),
            Value::VecScalar(eval_points_vec),
        ),
        (Vid("w".to_string()), Value::VecScalar(w_vec)),
        (Vid("r".to_string()), Value::VecScalar(r_vec)),
        (Vid("b".to_string()), Value::VecScalar(b_vec)),
        (Vid("c_sim".to_string()), Value::VecScalar(c_sim_vec)),
        (Vid("m2_sim".to_string()), Value::VecScalar(m2_sim_vec)),
        (Vid("u_points".to_string()), Value::VecScalar(u_points_vec)),
        (Vid("u_evals".to_string()), Value::VecScalar(u_evals_vec)),
    ])
}
