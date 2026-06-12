//! Side-by-side PARI timing: zippel vs. native garuda-pari port
//! (BLS12-381, Square R1CS).
//!
//! Both sides see the same K-constraint SR1CS instance with the
//! upstream "instance outliner" matrix layout — see `benchmarks::pari`
//! for the parity decisions.

use benchmarks::pari::{
    DEFAULT_K_VARS, DEFAULT_M_LOG, DEFAULT_N_PUB, Instance, inst_gen, native_side, zippel_side,
};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Side-by-side PARI timing: zippel vs. garuda-pari port (BLS12-381)")]
struct Args {
    /// log_2 of the number of constraints (K = 2^M).
    #[arg(long, default_value_t = DEFAULT_M_LOG)]
    m: usize,
    /// Number of public input variables (includes the implicit constant 1).
    #[arg(long, default_value_t = DEFAULT_N_PUB)]
    n: usize,
    /// Total number of variables (`num_vars = 2*n + m_witness`). With the
    /// instance-outliner layout, the witness portion is `num_vars - n`.
    #[arg(long, default_value_t = DEFAULT_K_VARS)]
    k_vars: usize,
    /// Comma-separated M values; if set, sweeps a grid (overrides --m).
    #[arg(long, value_delimiter = ',')]
    sweep_m: Option<Vec<usize>>,
}

fn main() {
    let args = Args::parse();
    let ms = args.sweep_m.unwrap_or_else(|| vec![args.m]);

    println!("=== PARI: zippel vs. native garuda-pari port (BLS12-381) ===");
    println!("statement: Square R1CS — (A·z) ∘ (A·z) = B·z on K = 2^M constraints");
    println!("layout:    upstream instance-outliner (last n constraints are e_i rows)");
    println!("native side  = pari_native (port of alireza-shirzad/garuda-pari)");
    println!("zippel side  = examples/pari/pari.zippel\n");
    println!(
        "  M |   K  | n |  k_v | zippel prove  zippel verify | native prove  native verify | proof | prove ratio  verify ratio"
    );
    println!(
        "----+------+---+------+-----------------------------+-----------------------------+-------+--------------------------"
    );

    for &m in &ms {
        let k = 1usize << m;
        let n = args.n;
        let k_vars = args.k_vars.max(2 * n + 1); // need room for aux + ≥1 witness
        // Build a fresh instance for this row.
        let mut rng = ark_std::test_rng();
        let m_witness = k_vars - 2 * n;
        let inst: Instance<_> = inst_gen::build_random(m, n, m_witness, &mut rng);

        let mut zs = zippel_side::Setup::new(m, n, &inst);
        let np = native_side::Setup::new(&inst);
        let zt = zs.time_protocol(&inst);
        let nt = np.time_protocol(&inst);
        let proof_bytes = np.proof_size(&inst);

        println!(
            " {m:>2} | {k:>4} | {n:>1} | {kv:>4} | {:>11.2?}  {:>13.2?} | {:>11.2?}  {:>13.2?} | {pb:>4}B | {:>10.2}x  {:>11.2}x",
            zt.prove,
            zt.verify,
            nt.prove,
            nt.verify,
            zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
            zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
            kv = inst.num_vars,
            pb = proof_bytes,
        );
    }
}
