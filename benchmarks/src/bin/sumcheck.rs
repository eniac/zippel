use benchmarks::sumcheck::{DEFAULT_MAX_DEGREE, DEFAULT_NUM_VARS, native_side, zippel_side};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side sumcheck timing: zippel vs. hyperplonk-native")]
struct Args {
    #[arg(long, default_value_t = DEFAULT_NUM_VARS)]
    num_vars: usize,
    #[arg(long, default_value_t = DEFAULT_MAX_DEGREE)]
    max_degree: usize,
    /// Comma-separated num_vars values; if set, sweeps a grid (overrides --num-vars).
    #[arg(long, value_delimiter = ',')]
    sweep_num_vars: Option<Vec<usize>>,
    /// Comma-separated max_degree values; if set, sweeps a grid (overrides --max-degree).
    #[arg(long, value_delimiter = ',')]
    sweep_max_degree: Option<Vec<usize>>,
}

fn main() {
    let args = Args::parse();
    let nvs = args.sweep_num_vars.unwrap_or_else(|| vec![args.num_vars]);
    let mds = args
        .sweep_max_degree
        .unwrap_or_else(|| vec![args.max_degree]);

    println!("=== Sumcheck: zippel vs. hyperplonk-native ===");
    println!("polynomial: base(x)^d where base is a random dense MLE");
    println!();
    println!(
        " nv  deg | zippel prove  zippel verify | hp prove   hp verify  | prove ratio  verify ratio"
    );
    println!(
        "---------+-----------------------------+-----------------------+--------------------------"
    );

    for &nv in &nvs {
        for &md in &mds {
            let mut z = zippel_side::Setup::new(nv, md);
            let n = native_side::Setup::new(nv, md);
            let zt = z.time_protocol();
            let nt = n.time_protocol();
            println!(
                " {nv:>2}  {md:>3} | {:>11.2?}  {:>13.2?} | {:>9.2?} {:>10.2?} | {:>10.2}x  {:>11.2}x",
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
