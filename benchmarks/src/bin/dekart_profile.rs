//! Prover-only timing of the zippel DeKART proto, cut off after each
//! protocol step, to attribute prover time without a sampling profiler.
//! Each variant keeps the full argument list and ends with prover messages
//! that consume the step's values, so nothing before the cut is dead code.

use benchmarks::dekart::{DEFAULT_ELL, shared, zippel_side};
use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value_t = 14)]
    log_n: usize,
    #[arg(long, default_value_t = DEFAULT_ELL)]
    ell: usize,
    #[arg(long, default_value_t = 3)]
    samples: u32,
    /// Proto files to time, in order (each a truncation of dekart.zippel).
    #[arg(required = true)]
    protos: Vec<PathBuf>,
}

fn main() {
    let args = Args::parse();
    let sh = shared::build(args.log_n, args.ell);
    let mut prev = std::time::Duration::ZERO;
    for p in &args.protos {
        let mut z = zippel_side::Setup::new_with_proto(&sh, p.clone());
        let t = z.time_prover_only(args.samples);
        println!(
            "{:<40} total {:>10.2?}   step {:>10.2?}",
            p.file_name().unwrap().to_string_lossy(),
            t,
            t.saturating_sub(prev)
        );
        prev = t;
    }
}
