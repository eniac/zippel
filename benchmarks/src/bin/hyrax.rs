//! Head-to-head benchmark of the Zippel-compiled Hyrax polynomial commitment against a
//! hand-rolled native implementation on BLS12-381.
//!
//! Both sides prove `p̃(z) = y` for a multilinear polynomial with `2^N` coefficients. The prover
//! timer covers the Pedersen row commitments plus the Schnorr-style proof of dot product; the
//! verifier timer covers the `T` reconstruction and the two group equality checks. `--sweep`
//! sweeps a grid of `N` values and `--nodes` additionally reports the scheduled prover and
//! verifier DAG node counts.

use benchmarks::hyrax::{DEFAULT_N, native_side, zippel_side};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side Hyrax timing: zippel vs hand-written native (BLS12-381)")]
struct Args {
    #[arg(long, default_value_t = DEFAULT_N)]
    n: usize,
    #[arg(long, value_delimiter = ',')]
    sweep: Option<Vec<usize>>,
    #[arg(long, default_value_t = false)]
    nodes: bool,
}

fn main() {
    let args = Args::parse();
    let ns = args.sweep.unwrap_or_else(|| vec![args.n]);

    println!("=== Hyrax: zippel vs. hand-written native (BLS12-381) ===");
    println!("statement: prove p̃(z) = y for multilinear p with 2^N coefficients");
    println!("zippel side    = templated `examples/hyrax/hyrax.zippel`");
    println!("native side    = hand-rolled (arkworks BLS12-381 + Blake2b FS)");
    println!("prove timer    = commit + open (Pedersen row commits + Schnorr-style PoDP)");
    println!("verify timer   = verify (T reconstruction + 2 group equalities)");
    println!();
    if args.nodes {
        println!(
            "  N |  2^N    | zippel prove   zippel verify | native prove   native verify | prove ratio  verify ratio | prover nodes  verifier nodes"
        );
        println!(
            "----+---------+-----------------------------+-----------------------------+--------------------------+-----------------------------"
        );
    } else {
        println!(
            "  N |  2^N    | zippel prove   zippel verify | native prove   native verify | prove ratio  verify ratio"
        );
        println!(
            "----+---------+-----------------------------+-----------------------------+-------------------------"
        );
    }

    for &n in &ns {
        let mut z = zippel_side::Setup::new(n);
        let np = native_side::Setup::new(n);
        let (pnodes, vnodes) = z.graph_sizes();
        let zt = z.time_protocol();
        let nt = np.time_protocol();
        let size = 1usize << n;
        if args.nodes {
            println!(
                " {n:>2} | {size:>7} | {:>11.2?}  {:>13.2?} | {:>11.2?}  {:>13.2?} | {:>10.2}x  {:>11.2}x | {pnodes:>12}  {vnodes:>14}",
                zt.prove,
                zt.verify,
                nt.prove,
                nt.verify,
                zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
                zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
            );
        } else {
            println!(
                " {n:>2} | {size:>7} | {:>11.2?}  {:>13.2?} | {:>11.2?}  {:>13.2?} | {:>10.2}x  {:>11.2}x",
                zt.prove,
                zt.verify,
                nt.prove,
                nt.verify,
                zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
                zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
            );
        }
    }
}
