use benchmarks::dekart::{DEFAULT_ELL, DEFAULT_LOG_N, native_side, shared, zippel_side};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(
    about = "Side-by-side DeKART range proof timing: zippel vs. Aptos dekart_univariate_v2 (BLS12-381)"
)]
struct Args {
    /// log2 of the domain size; proves n = 2^L - 1 values.
    #[arg(long, default_value_t = DEFAULT_LOG_N)]
    log_n: usize,
    /// Comma-separated L values; if set, sweeps a grid (overrides --log-n).
    #[arg(long, value_delimiter = ',')]
    sweep: Option<Vec<usize>>,
    /// Bit width: each value is in [0, 2^ell).
    #[arg(long, default_value_t = DEFAULT_ELL)]
    ell: usize,
}

fn main() {
    let args = Args::parse();
    let ls = args.sweep.unwrap_or_else(|| vec![args.log_n]);

    println!(
        "=== DeKART: zippel vs. Aptos dekart_univariate_v2 (BLS12-381, ell={}) ===",
        args.ell
    );
    println!("prove timer = prove only (com_f is the public statement on both sides)");
    println!();
    println!(
        "   L       n | zippel prove  zippel verify | native prove  native verify | prove ratio  verify ratio"
    );
    println!(
        "-------------+-----------------------------+-----------------------------+--------------------------"
    );

    for &l in &ls {
        let sh = shared::build(l, args.ell);
        let mut z = zippel_side::Setup::new(&sh);
        let np = native_side::Setup::new(&sh);
        let nt = np.time_protocol();
        let zt = z.time_protocol();
        println!(
            "  {l:>2} {:>7} | {:>11.2?}  {:>13.2?} | {:>11.2?}  {:>13.2?} | {:>10.2}x  {:>11.2}x",
            sh.n,
            zt.prove_mean(),
            zt.verify_mean(),
            nt.prove_mean(),
            nt.verify_mean(),
            zt.prove_mean().as_secs_f64() / nt.prove_mean().as_secs_f64(),
            zt.verify_mean().as_secs_f64() / nt.verify_mean().as_secs_f64(),
        );
    }
}
