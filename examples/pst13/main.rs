use ark_std::One;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

const DEFAULT_N: usize = 2;

fn main() {
    let n: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_N);
    assert!(
        (1..=20).contains(&n),
        "N must be in 1..=20 (pst13.zippel helpers cap at K=20)"
    );

    println!("=== PST13 Multilinear PCS (ArkBls12_381, N={n}) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &n);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(n);
    common::run_prover_and_verify(&mut handler, inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
    common::time_analysis!(
        "Soundness",
        analysis_handler.analyze_special_soundness(vec![2])
    );
}

fn prover_create_inputs(n: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let size = 1usize << n;

    let gen_g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let gen_h = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);

    let one = <ArkBls12_381 as ArkConfig>::F::one();
    let alpha: Vec<_> = (0..n)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let one_m_alpha: Vec<_> = alpha.iter().map(|a| one - a).collect();

    let ck_n_scalars: Vec<_> = (0..size)
        .map(|i| {
            (0..n).fold(one, |acc, j| {
                let bit = (i >> (n - 1 - j)) & 1;
                if bit == 1 {
                    acc * alpha[j]
                } else {
                    acc * one_m_alpha[j]
                }
            })
        })
        .collect();
    let ck_n = Value::VecG1(ck_n_scalars.iter().map(|s| gen_g * s).collect());

    let p_scalars: Vec<_> = (0..size)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let p = Value::VecScalar(p_scalars.clone());

    let z_scalars: Vec<_> = (0..n)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let z = Value::VecScalar(z_scalars.clone());

    let y_val = (0..size).fold(<ArkBls12_381 as ArkConfig>::F::from(0u64), |acc, i| {
        let eq_z_i = (0..n).fold(one, |prod, j| {
            let bit = (i >> (n - 1 - j)) & 1;
            if bit == 1 {
                prod * z_scalars[j]
            } else {
                prod * (one - z_scalars[j])
            }
        });
        acc + p_scalars[i] * eq_z_i
    });
    let y = Value::Scalar(y_val);

    let alpha_h = Value::VecG2(alpha.iter().map(|a| gen_h * a).collect());

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ck_N".to_string()), ck_n),
        (Vid("g_gen".to_string()), Value::G1(gen_g)),
        (Vid("h_gen".to_string()), Value::G2(gen_h)),
        (Vid("alpha_H".to_string()), alpha_h),
        (Vid("alpha".to_string()), Value::VecScalar(alpha.clone())),
    ])
}
