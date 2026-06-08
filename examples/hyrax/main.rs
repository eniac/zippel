use ark_std::One;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

const L: usize = 2;
const M: usize = 2;
const NROWS: usize = 1 << L;
const NCOLS: usize = 1 << M;
const NTOT: usize = NROWS * NCOLS;

type F = <ArkBls12_381 as ArkConfig>::F;
type G1 = <ArkBls12_381 as ArkConfig>::G1;

fn main() {
    println!("=== Hyrax PCS (ArkBls12_381) — L={L}, M={M}, NTOT={NTOT} ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hyrax/hyrax.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let t = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    println!("Prover time:    {:.2?}", t.elapsed());
    println!("Proof items:    {}", proof.len());

    let verifier_scheduled = handler.default_schedule_verifier();
    let t = Instant::now();
    let verifier_result = handler
        .run_verifier(verifier_scheduled, proof)
        .expect("run_verifier failed");
    println!("Verifier time:  {:.2?}", t.elapsed());

    let result = check_verification(verifier_result);
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let one = F::one();

    let p: Vec<F> = (0..NTOT).map(|_| F::rand(&mut rng)).collect();
    let z_row: Vec<F> = (0..L).map(|_| F::rand(&mut rng)).collect();
    let z_col: Vec<F> = (0..M).map(|_| F::rand(&mut rng)).collect();

    let l_vec = eq_evals(&z_row, one);
    let r_vec = eq_evals(&z_col, one);
    let y: F = (0..NROWS)
        .flat_map(|i| (0..NCOLS).map(move |j| (i, j)))
        .map(|(i, j)| l_vec[i] * r_vec[j] * p[i * NCOLS + j])
        .sum();

    let g_vec: Vec<G1> = (0..NCOLS).map(|_| G1::rand(&mut rng)).collect();
    let g_base = G1::rand(&mut rng);
    let h_base = G1::rand(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), Value::VecScalar(p)),
        (Vid("z_row".to_string()), Value::VecScalar(z_row)),
        (Vid("z_col".to_string()), Value::VecScalar(z_col)),
        (Vid("y".to_string()), Value::Scalar(y)),
        (Vid("g_vec".to_string()), Value::VecG1(g_vec)),
        (Vid("g_base".to_string()), Value::G1(g_base)),
        (Vid("h_base".to_string()), Value::G1(h_base)),
    ])
}

fn eq_evals(x: &[F], one: F) -> Vec<F> {
    let n = x.len();
    let mut out = vec![one; 1 << n];
    let mut size = 1;
    for &xi in x {
        let one_m_xi = one - xi;
        for i in (0..size).rev() {
            let v = out[i];
            out[size + i] = v * xi;
            out[i] = v * one_m_xi;
        }
        size *= 2;
    }
    out
}
