// Standalone test: 3-var sumcheck on (Az·Bz − Cz)·eq_tau with
// inputs built from a random satisfying R1CS (matching Spartan
// sum-check #1 verbatim).

use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use rand::Rng;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

const STACK: usize = 64 * 1024 * 1024;
const M: usize = 3;
const NUM_CONS: usize = 1 << M;
const W_LEN: usize = 1 << (M - 1);
const IO_LEN: usize = W_LEN - 1;

fn main() {
    thread::Builder::new()
        .name("sc-test-m3".into())
        .stack_size(STACK)
        .spawn(run)
        .expect("spawn")
        .join()
        .expect("join");
}

fn run() {
    let zippel_file = PathBuf::from(
        std::env::var("SC_TEST_M3_FILE").unwrap_or_else(|_| "/tmp/sc_test_m3.zippel".to_string()),
    );
    eprintln!("using zippel file: {}", zippel_file.display());

    let args = ZippelArgs::new(zippel_file);
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    type G2 = <ArkBls12_381 as ArkConfig>::G2;
    let mut rng = rand::rngs::OsRng;
    let one = F::from(1u64);

    let w: Vec<F> = (0..W_LEN).map(|_| F::rand(&mut rng)).collect();
    let io: Vec<F> = (0..IO_LEN).map(|_| F::rand(&mut rng)).collect();
    let mut z: Vec<F> = Vec::with_capacity(NUM_CONS);
    z.extend_from_slice(&w);
    z.extend_from_slice(&io);
    z.push(one);

    let r1cs = random_r1cs(&mut rng, NUM_CONS, &z);
    let ck_n_w: Vec<G1> = (0..W_LEN).map(|_| G1::rand(&mut rng)).collect();
    let g_gen = G1::rand(&mut rng);
    let h_gen = G2::rand(&mut rng);
    let alpha_h_w: Vec<G2> = (0..(M - 1)).map(|_| G2::rand(&mut rng)).collect();

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("mat_a".to_string()), Value::VecScalar(r1cs.0)),
        (Vid("mat_b".to_string()), Value::VecScalar(r1cs.1)),
        (Vid("mat_c".to_string()), Value::VecScalar(r1cs.2)),
        (Vid("io".to_string()), Value::VecScalar(io)),
        (Vid("w".to_string()), Value::VecScalar(w)),
        (Vid("ck_n_w".to_string()), Value::VecG1(ck_n_w)),
        (Vid("g_gen".to_string()), Value::G1(g_gen)),
        (Vid("h_gen".to_string()), Value::G2(h_gen)),
        (Vid("alpha_h_w".to_string()), Value::VecG2(alpha_h_w)),
        (Vid("f_one".to_string()), Value::Scalar(one)),
    ]);

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    println!("Prover:   {prover_elapsed:.2?}");

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(verifier_scheduled, proof)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    println!("Verifier: {verifier_elapsed:.2?}");

    for (i, v) in verifier_result.iter().enumerate() {
        if let Value::Bool(b) = v {
            println!("  verify[{i}] = {b}");
        }
    }
    let passed = check_verification(verifier_result).passed;
    println!("Verdict: {}", if passed { "PASS" } else { "FAIL" });
    if !passed {
        std::process::exit(1);
    }
}

type F = <ArkBls12_381 as ArkConfig>::F;
fn random_r1cs<R: Rng + ?Sized>(rng: &mut R, m: usize, z: &[F]) -> (Vec<F>, Vec<F>, Vec<F>) {
    let mut a = vec![F::from(0u64); m * m];
    let mut b = vec![F::from(0u64); m * m];
    let mut c = vec![F::from(0u64); m * m];
    let cc = m - 1; // const column
    for i in 0..m {
        let a_row: Vec<F> = (0..m).map(|_| F::rand(rng)).collect();
        let b_row: Vec<F> = (0..m).map(|_| F::rand(rng)).collect();
        let mut c_row: Vec<F> = (0..m).map(|_| F::rand(rng)).collect();
        let az: F = a_row.iter().zip(z.iter()).map(|(x, y)| *x * *y).sum();
        let bz: F = b_row.iter().zip(z.iter()).map(|(x, y)| *x * *y).sum();
        let other: F = c_row
            .iter()
            .zip(z.iter())
            .enumerate()
            .filter(|(j, _)| *j != cc)
            .map(|(_, (c, zj))| *c * *zj)
            .sum();
        c_row[cc] = az * bz - other;
        for j in 0..m {
            a[i * m + j] = a_row[j];
            b[i * m + j] = b_row[j];
            c[i * m + j] = c_row[j];
        }
    }
    (a, b, c)
}
