//! curve25519-dalek 4 (libspartan's) against 5 (`DalekRistretto`'s): the same
//! variable-time Ristretto MSM at the sizes Spartan's prover commits, so a
//! difference between the two Spartan rows of `bench_all` is not credited to
//! Zippel when it is dalek's. The 5 side goes through the backend's
//! `Group::msm`, as the runtime calls it.
//!
//! ```sh
//! RAYON_NUM_THREADS=8 cargo run --release -p experiments --bin dalek_msm
//! ```

use backend::{Backend, DalekRistretto, Field, Group};
use clap::Parser;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(about = "Ristretto MSM: curve25519-dalek 4 vs. 5")]
struct Args {
    /// log2 of the MSM sizes to measure.
    #[arg(long, value_delimiter = ',', default_values_t = [8, 10, 12, 14, 16])]
    log_n: Vec<usize>,
    /// Runs per measurement; the median is reported.
    #[arg(long, default_value_t = 7)]
    reps: usize,
}

fn median(reps: usize, mut f: impl FnMut()) -> Duration {
    let mut times: Vec<Duration> = (0..reps)
        .map(|_| {
            let t = Instant::now();
            f();
            t.elapsed()
        })
        .collect();
    times.sort();
    times[reps / 2]
}

fn main() {
    let args = Args::parse();
    let mut rng = StdRng::seed_from_u64(7);
    println!("log_n,dalek4_ms,dalek5_ms");
    for &log_n in &args.log_n {
        let n = 1 << log_n;
        let bases: Vec<<DalekRistretto as Backend>::G1> =
            (0..n).map(|_| Group::rand(&mut rng)).collect();
        let scalars: Vec<<DalekRistretto as Backend>::F> =
            (0..n).map(|_| Field::rand(&mut rng)).collect();
        // The same points and scalars in dalek 4, by their canonical encodings.
        let bases4: Vec<curve25519_dalek::RistrettoPoint> = bases
            .iter()
            .map(|b| {
                let mut bytes = Vec::new();
                b.write_bytes(&mut bytes);
                curve25519_dalek::ristretto::CompressedRistretto::from_slice(&bytes)
                    .unwrap()
                    .decompress()
                    .unwrap()
            })
            .collect();
        let scalars4: Vec<curve25519_dalek::Scalar> = scalars
            .iter()
            .map(|s| {
                let mut bytes = [0u8; 32];
                let mut v = Vec::new();
                s.write_bytes(&mut v);
                bytes.copy_from_slice(&v);
                curve25519_dalek::Scalar::from_canonical_bytes(bytes).unwrap()
            })
            .collect();
        let r5 = <DalekRistretto as Backend>::G1::msm(&bases, &scalars);
        let r4 = curve25519_dalek::RistrettoPoint::vartime_multiscalar_mul(&scalars4, &bases4);
        let mut b5 = Vec::new();
        r5.write_bytes(&mut b5);
        assert_eq!(b5, r4.compress().as_bytes(), "the two MSMs disagree");
        let t4 = median(args.reps, || {
            std::hint::black_box(curve25519_dalek::RistrettoPoint::vartime_multiscalar_mul(
                &scalars4, &bases4,
            ));
        });
        let t5 = median(args.reps, || {
            std::hint::black_box(<DalekRistretto as Backend>::G1::msm(&bases, &scalars));
        });
        println!(
            "{log_n},{:.3},{:.3}",
            t4.as_secs_f64() * 1e3,
            t5.as_secs_f64() * 1e3
        );
    }
}
