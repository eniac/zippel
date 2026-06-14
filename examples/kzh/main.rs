use ark_ff::Zero;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

const NX: usize = 2;
const NY: usize = 2;

fn main() {
    println!("=== KZH (ArkBls12_381, NX={}, NY={}) ===", NX, NY);
    let args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
    let compile_result = std::panic::catch_unwind(|| {
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let sizes = Ctx::new();
        handler.compile(&sizes);
        handler
    });

    let mut handler = match compile_result {
        Ok(h) => h,
        Err(e) => {
            println!("Compilation:    ✗ KZH protocol has syntax not yet supported by the compiler");
            if let Some(msg) = e.downcast_ref::<String>() {
                println!("  Error: {}", msg);
            }
            std::process::exit(0);
        }
    };

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let sizes = Ctx::new();
    analysis_handler.compile(&sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let g2_base = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let alpha = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let h_xy_size = 1usize << (NX + NY);
    let h_y_size = 1usize << NY;
    let d_x_size = 1usize << NX;

    let g_cols: Vec<<ArkBls12_381 as ArkConfig>::G1> = (0..h_y_size)
        .map(|_| <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng))
        .collect();
    let tau_rows: Vec<<ArkBls12_381 as ArkConfig>::F> = (0..d_x_size)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();

    let h_xy_vals: Vec<_> = (0..h_xy_size)
        .map(|k| {
            let i = k >> NY;
            let j = k & (h_y_size - 1);
            g_cols[j] * tau_rows[i]
        })
        .collect();
    let h_y_vals: Vec<_> = (0..h_y_size).map(|j| g_cols[j] * alpha).collect();

    let v_prime = g2_base * alpha;
    let v_x_vals: Vec<_> = (0..d_x_size).map(|i| g2_base * tau_rows[i]).collect();

    let f_evals: Vec<<ArkBls12_381 as ArkConfig>::F> = (0..h_xy_size)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();

    let d_x_vals: Vec<_> = (0..d_x_size)
        .map(|i| {
            let mut acc = <ArkBls12_381 as ArkConfig>::G1::zero();
            for j in 0..h_y_size {
                acc += h_y_vals[j] * f_evals[i * h_y_size + j];
            }
            acc
        })
        .collect();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evals".to_string()), Value::VecScalar(f_evals)),
        (Vid("h_xy".to_string()), Value::VecG1(h_xy_vals)),
        (Vid("h_y".to_string()), Value::VecG1(h_y_vals)),
        (Vid("d_x".to_string()), Value::VecG1(d_x_vals)),
        (Vid("v_prime".to_string()), Value::G2(v_prime)),
        (Vid("v_x".to_string()), Value::VecG2(v_x_vals)),
    ])
}
