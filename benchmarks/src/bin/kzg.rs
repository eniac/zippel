use benchmarks::kzg::{DEFAULT_N, native_side, zippel_side};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side KZG timing: zippel vs. ark-poly-commit KZG10 (BLS12-381)")]
struct Args {
    /// Number of polynomial coefficients N (poly degree = N - 1).
    #[arg(long, default_value_t = DEFAULT_N)]
    n: usize,
    /// Comma-separated N values; if set, sweeps a grid (overrides --n).
    #[arg(long, value_delimiter = ',')]
    sweep_n: Option<Vec<usize>>,
    /// Diagnostic: drop the .zippel `where` clause SRS structure check
    /// (N-1 pairings) so zippel's verifier only runs the protocol body.
    #[arg(long)]
    no_srs_check: bool,
}

fn main() {
    let args = Args::parse();
    let ns = args.sweep_n.unwrap_or_else(|| vec![args.n]);

    println!("=== KZG: zippel vs. ark-poly-commit KZG10 (BLS12-381) ===");
    println!("statement: prove p(z)=v for poly of degree N-1");
    println!("prove timer = commit + open (matches zippel's protocol scope)");
    println!();
    println!(
        "    N | zippel prove  zippel verify | pc prove   pc verify  | prove ratio  verify ratio"
    );
    println!(
        "------+-----------------------------+-----------------------+--------------------------"
    );

    if args.no_srs_check {
        println!("(diagnostic mode: zippel .zippel rendered without SRS structure check)\n");
    }

    for &n in &ns {
        let mut z = zippel_side::Setup::new_with(n, args.no_srs_check);
        let np = native_side::Setup::new(n);
        let zt = z.time_protocol();
        let nt = np.time_protocol();
        println!(
            "  {n:>3} | {:>11.2?}  {:>13.2?} | {:>9.2?} {:>10.2?} | {:>10.2}x  {:>11.2}x",
            zt.prove,
            zt.verify,
            nt.prove,
            nt.verify,
            zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
            zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
        );
    }
}
