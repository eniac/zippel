//! Microbenchmarks of multi-scalar multiplication: native arkworks against
//! zippel's backend call and against a zippel protocol run end to end.
//!
//! 1. One MSM: native `G1Projective::msm`, the backend's `vec_dot` (no
//!    runtime), and a protocol computing one `dot` through the runtime.
//! 2. Three independent MSMs: native runs them in sequence; the protocol
//!    computes three `dot`s, which the runtime may run concurrently.
//!
//! Inputs are 2^`--log-n` random BLS12-381 scalars and affine G1 points. Each
//! time is the median of `--reps` runs, and every zippel result is checked
//! against native's. `RAYON_NUM_THREADS` sets the thread budget.
//!
//! ```sh
//! RAYON_NUM_THREADS=1 cargo run --release -p benchmarks --bin msm_micro
//! ```

use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use clap::Parser;
use lang::id::{Tid, Vid};
use rand::SeedableRng;
use rand::rngs::StdRng;
use share::Ctx;
use std::io::Write;
use std::time::{Duration, Instant};
use zippel::{ZippelArgs, ZippelHandler};

type C = ArkBls12_381;

#[derive(Parser, Debug)]
#[command(about = "MSM microbenchmarks: native arkworks vs. zippel")]
struct Args {
    /// log2 of the MSM size.
    #[arg(long, default_value_t = 14)]
    log_n: usize,
    /// Runs per measurement; the median is reported.
    #[arg(long, default_value_t = 5)]
    reps: usize,
}

const ONE_MSM: &str = "
proto msm1<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>, N: Size>(
    witness s1: [F; N],
    extra b1: [G1; N],
) where 1 == 1 {
    c <- dot(s1, b1);
    verify(c == c)
}";

const THREE_MSMS: &str = "
proto msm3<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>, N: Size>(
    witness s1: [F; N],
    witness s2: [F; N],
    witness s3: [F; N],
    extra b1: [G1; N],
    extra b2: [G1; N],
    extra b3: [G1; N],
) where 1 == 1 {
    let d1 = dot(s1, b1);
    let d2 = dot(s2, b2);
    let d3 = dot(s3, b3);
    c <- d1 + d2 + d3;
    verify(c == c)
}";

fn main() {
    let args = Args::parse();
    let n = 1usize << args.log_n;
    let mut rng = StdRng::seed_from_u64(1);
    let scalars: Vec<Vec<Fr>> = (0..3)
        .map(|_| (0..n).map(|_| Fr::rand(&mut rng)).collect())
        .collect();
    let bases: Vec<Vec<G1Affine>> = (0..3)
        .map(|_| {
            let points: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
            G1Projective::normalize_batch(&points)
        })
        .collect();
    let native = |i: usize| G1Projective::msm(&bases[i], &scalars[i]).expect("msm");
    let inputs = |count: usize| -> Vec<(Vid, Value<C>)> {
        (0..count)
            .flat_map(|i| {
                [
                    (
                        Vid(format!("s{}", i + 1)),
                        Value::vec_scalar(scalars[i].clone()),
                    ),
                    (
                        Vid(format!("b{}", i + 1)),
                        Value::vec_g1_affine(bases[i].clone()),
                    ),
                ]
            })
            .collect()
    };

    println!(
        "MSM microbenchmarks: 2^{} BLS12-381 G1, {} rayon thread(s), median of {}",
        args.log_n,
        rayon::current_num_threads(),
        args.reps
    );

    let (mut handler, _source) = compile(ONE_MSM, n);
    let one = inputs(1);
    let expected = native(0);
    assert_eq!(
        <C as ArkConfig>::G1Ops::vec_dot(&bases[0], &scalars[0]),
        expected
    );
    assert_eq!(
        handler.run_prover(one.clone()).expect("prover")[0],
        Value::g1(expected)
    );
    println!("1 MSM ({})", node_kinds(&handler));
    report("native msm", median(args.reps, || native(0)));
    report(
        "zippel backend dot",
        median(args.reps, || {
            <C as ArkConfig>::G1Ops::vec_dot(&bases[0], &scalars[0])
        }),
    );
    report(
        "zippel protocol",
        median(args.reps, || {
            handler.run_prover(one.clone()).expect("prover")
        }),
    );

    let (mut handler, _source) = compile(THREE_MSMS, n);
    let three = inputs(3);
    let expected = native(0) + native(1) + native(2);
    assert_eq!(
        handler.run_prover(three.clone()).expect("prover")[0],
        Value::g1(expected)
    );
    println!("3 MSMs ({})", node_kinds(&handler));
    report(
        "native, in sequence",
        median(args.reps, || native(0) + native(1) + native(2)),
    );
    report(
        "zippel protocol",
        median(args.reps, || {
            handler.run_prover(three.clone()).expect("prover")
        }),
    );
}

/// Compiles the protocol `source` with `N = n`. The returned file holds the
/// source and must outlive the handler.
fn compile(source: &str, n: usize) -> (ZippelHandler<C>, tempfile::NamedTempFile) {
    let mut file = tempfile::Builder::new()
        .suffix(".zippel")
        .tempfile()
        .expect("temp file");
    file.write_all(source.as_bytes()).expect("write protocol");
    let mut handler = ZippelHandler::new(ZippelArgs::new(file.path().to_path_buf()));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &n);
    handler.compile(&sizes);
    (handler, file)
}

/// The prover graph's op and transcript node counts.
fn node_kinds(handler: &ZippelHandler<C>) -> String {
    let g = handler.prover_graph();
    let ops = g.node_indices().filter(|n| g[*n].is_op()).count();
    let transcript = g.node_indices().filter(|n| g[*n].is_transcript()).count();
    format!("{ops} op + {transcript} transcript nodes")
}

/// The median wall time of `reps` runs of `f`; its result is kept observable
/// so the work cannot be optimized away.
fn median<T>(reps: usize, mut f: impl FnMut() -> T) -> Duration {
    let mut times: Vec<Duration> = (0..reps)
        .map(|_| {
            let start = Instant::now();
            std::hint::black_box(f());
            start.elapsed()
        })
        .collect();
    times.sort();
    times[reps / 2]
}

fn report(label: &str, time: Duration) {
    println!("  {label:22}{:8.1} ms", time.as_secs_f64() * 1e3);
}
