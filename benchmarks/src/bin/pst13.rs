//! Side-by-side PST13 timing: zippel-compiled `examples/pst13/pst13.zippel`
//! vs. EspressoSystems/hyperplonk's `MultilinearKzgPCS` (= PST13 under a
//! different name). Sweep knob is `n` = number of variables (= log_2(poly size)).

use benchmarks::pst13::{DEFAULT_N, native_side, shared, zippel_side};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side PST13 timing: zippel vs. hyperplonk MultilinearKzgPCS (BLS12-381)")]
struct Args {
    /// Number of variables N (polynomial has 2^N coefficients).
    #[arg(long, default_value_t = DEFAULT_N)]
    n: usize,
    /// Comma-separated N values; if set, sweeps a grid (overrides --n).
    #[arg(long, value_delimiter = ',')]
    sweep: Option<Vec<usize>>,
}

fn main() {
    let args = Args::parse();
    let ns = args.sweep.unwrap_or_else(|| vec![args.n]);

    println!("=== PST13: zippel vs. hyperplonk MultilinearKzgPCS (BLS12-381) ===");
    println!("statement: prove p̃(z) = y for multilinear p with 2^N coefficients");
    println!("zippel side    = examples/pst13/pst13.zippel");
    println!("native side    = subroutines::pcs::multilinear_kzg::MultilinearKzgPCS (hp-ark v0.4)");
    println!("prove timer    = commit + open");
    println!("verify timer   = verify (single pairing check)");
    println!();
    println!(
        "  N |  2^N    | zippel prove   zippel verify | native prove   native verify | prove ratio  verify ratio"
    );
    println!(
        "----+---------+-----------------------------+-----------------------------+-------------------------"
    );

    for &n in &ns {
        let shared = shared::build(n);
        let mut z = zippel_side::Setup::new(&shared);
        let np = native_side::Setup::new(&shared);
        let zt = z.time_protocol();
        let nt = np.time_protocol();
        let size = 1usize << n;
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
