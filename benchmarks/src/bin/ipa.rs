use benchmarks::ipa::{native_side, zippel_side};
use clap::Parser;

const DEFAULT_S: usize = 6;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side IPA timing: zippel vs. ark-poly-commit IpaPC (Secp256k1)")]
struct Args {
    /// S, where vector size N = 2^S.
    #[arg(long, default_value_t = DEFAULT_S)]
    s: usize,
    /// Comma-separated S values; if set, sweeps a grid (overrides --s).
    #[arg(long, value_delimiter = ',')]
    sweep_s: Option<Vec<usize>>,
}

fn main() {
    let args = Args::parse();
    let ss = args.sweep_s.unwrap_or_else(|| vec![args.s]);

    println!("=== IPA: zippel vs. ark-poly-commit IpaPC (Secp256k1) ===");
    println!("vector size N = 2^S; both sides verify internally");
    println!();
    println!(
        "  S    N | zippel prove  zippel verify | pc prove   pc verify  | prove ratio  verify ratio"
    );
    println!(
        "---------+-----------------------------+-----------------------+--------------------------"
    );

    for &s in &ss {
        let n = 1usize << s;
        let mut z = zippel_side::Setup::new(s);
        let np = native_side::Setup::new(s);
        let zt = z.time_protocol();
        let nt = np.time_protocol();
        println!(
            "  {s:>2}  {n:>4} | {:>11.2?}  {:>13.2?} | {:>9.2?} {:>10.2?} | {:>10.2}x  {:>11.2}x",
            zt.prove,
            zt.verify,
            nt.prove,
            nt.verify,
            zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
            zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
        );
    }
}
