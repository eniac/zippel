//! Side-by-side Groth16 timing: zippel vs. ark-groth16 v0.5
//! (BLS12-381).
//!
//! Both sides prove the same R1CS instance (`BenchCircuit`: each row is
//! `w1 * w2 = out`, with `out` a public input). Shared setup lives in
//! `benchmarks::groth16::shared`; the zippel side byte-translates the
//! v0.5 proving/verifying keys into git-main types and runs against
//! `examples/groth16/groth16-opt.zippel`.

use benchmarks::groth16::{DEFAULT_LOG_CONSTRAINTS, native_side, shared, zippel_side};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side Groth16 timing: zippel vs. ark-groth16 v0.5 (BLS12-381)")]
struct Args {
    /// log_2 of the number of R1CS constraints.
    #[arg(long, default_value_t = DEFAULT_LOG_CONSTRAINTS)]
    log_size: usize,
    /// Comma-separated log_size values; if set, sweeps a grid (overrides --log-size).
    #[arg(long, value_delimiter = ',')]
    sweep: Option<Vec<usize>>,
}

fn main() {
    let args = Args::parse();
    let log_sizes = args.sweep.unwrap_or_else(|| vec![args.log_size]);

    println!("=== Groth16: zippel vs. ark-groth16 v0.5 (BLS12-381) ===");
    println!("statement: BenchCircuit — N multiplication constraints w1*w2 = out");
    println!("native side  = ark-groth16 v0.5 (crates.io)");
    println!("zippel side  = examples/groth16/groth16-opt.zippel\n");
    println!(
        "  log |    C    |  M  |  L  | zippel prove   zippel verify | native prove   native verify | prove ratio  verify ratio"
    );
    println!(
        "------+---------+-----+-----+-----------------------------+-----------------------------+-------------------------"
    );

    for &log_size in &log_sizes {
        let num_constraints = 1usize << log_size;
        let s = shared::build(num_constraints);
        let m = s.vk.gamma_abc_g1.len();
        let l = s.pk.l_query.len();

        let mut zs = zippel_side::Setup::new(&s);
        let ns = native_side::Setup::new(&s);
        let zt = zs.time_protocol();
        let nt = ns.time_protocol();

        println!(
            " {log_size:>3} | {c:>7} | {m:>3} | {l:>3} | {:>11.2?}  {:>13.2?} | {:>11.2?}  {:>13.2?} | {:>10.2}x  {:>11.2}x",
            zt.prove,
            zt.verify,
            nt.prove,
            nt.verify,
            zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
            zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
            c = num_constraints,
        );
    }
}
