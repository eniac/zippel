//! Native Microsoft/Spartan baseline driver.
//!
//! Sweeps both the **NIZK** and **SNARK** variants from
//! https://github.com/microsoft/Spartan over a square-R1CS size grid.
//! For each `M` in the sweep:
//!   * `num_cons = num_vars = 2^M` (square)
//!   * `num_inputs = 1` (matches the zippel-side |io| at M = 2)
//!   * `num_nz_entries = num_cons` (one nonzero per row on average —
//!     Spartan's `produce_synthetic_r1cs` builds matrices in this shape;
//!     this is also what their own benches use)
//!
//! `--csv PATH` appends `variant,m,num_constraints,num_vars,num_inputs,nnz,
//! setup_ms,prover_ms,verifier_ms,proof_bytes,passed` per (variant, M).
//!
//! Variants:
//!   --variant nizk | snark | both    (default: both)
//!
//! NB: Spartan's `SNARK::prove` includes both the satisfiability sub-proof
//! AND the SPARK eval proof (i.e., the sparse-MLE opening of the
//! computation commitments to A, B, C); we time the full `prove` call,
//! mirroring how the harness times zippel's prove end-to-end.

use clap::Parser;
use libspartan::{Instance, NIZK, NIZKGens, SNARK, SNARKGens};
use merlin::Transcript;
use std::{
    fs::OpenOptions,
    io::Write,
    path::Path,
    time::{Duration, Instant},
};

#[derive(Parser, Debug, Clone)]
#[command(
    name = "spartan",
    about = "Native microsoft/Spartan NIZK + SNARK sweep"
)]
struct Args {
    /// Inclusive lower bound on M (log2 num_constraints). Default 2.
    #[arg(long, default_value_t = 2)]
    m_lo: u32,
    /// Inclusive upper bound on M. Default 20.
    #[arg(long, default_value_t = 20)]
    m_hi: u32,
    /// Number of instance inputs (|io|).
    #[arg(long, default_value_t = 1)]
    num_inputs: usize,
    /// "nizk", "snark", or "both" (default).
    #[arg(long, default_value = "both")]
    variant: String,
    /// CSV output path (or "-" for stdout). Appends if file exists.
    #[arg(long)]
    csv: Option<String>,
}

#[derive(Clone, Debug)]
struct Row {
    variant: &'static str,
    m: u32,
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    nnz: usize,
    setup: Duration,
    prover: Duration,
    verifier: Duration,
    proof_bytes: usize,
    passed: bool,
}

fn main() {
    let args = Args::parse();
    assert!(args.m_lo >= 1 && args.m_hi >= args.m_lo);
    let do_nizk = args.variant == "nizk" || args.variant == "both";
    let do_snark = args.variant == "snark" || args.variant == "both";
    assert!(do_nizk || do_snark, "--variant must be nizk/snark/both");

    println!(
        "=== Native microsoft/Spartan sweep (M = {}..={}, |io| = {}) ===",
        args.m_lo, args.m_hi, args.num_inputs,
    );
    println!(
        "variants: {}",
        match args.variant.as_str() {
            "nizk" => "NIZK only",
            "snark" => "SNARK only",
            _ => "NIZK + SNARK",
        }
    );

    let mut rows: Vec<Row> = Vec::new();
    for m in args.m_lo..=args.m_hi {
        let num_cons = 1usize << m;
        let num_vars = num_cons; // square R1CS
        let num_inputs = args.num_inputs;
        let nnz = num_cons; // matches their produce_synthetic_r1cs shape

        // Build the R1CS instance once per M (reused for both variants).
        let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
        let is_sat = inst.is_sat(&vars, &inputs).expect("is_sat failed");
        assert!(is_sat, "synthetic R1CS not satisfying at M={m}");

        if do_nizk {
            let r = run_nizk(m, num_cons, num_vars, num_inputs, &inst, &vars, &inputs);
            rows.push(r.clone());
            println!(
                "[NIZK]  M={m:>2} cons={c:>9} vars={v:>9} setup={s:>9.2?} prover={p:>10.2?} verifier={vt:>10.2?} proof={b:>8}B verdict={vd}",
                c = r.num_cons,
                v = r.num_vars,
                s = r.setup,
                p = r.prover,
                vt = r.verifier,
                b = r.proof_bytes,
                vd = if r.passed { "PASS" } else { "FAIL" },
            );
        }
        if do_snark {
            let r = run_snark(
                m,
                num_cons,
                num_vars,
                num_inputs,
                nnz,
                &inst,
                vars.clone(),
                &inputs,
            );
            rows.push(r.clone());
            println!(
                "[SNARK] M={m:>2} cons={c:>9} vars={v:>9} nnz={n:>9} setup={s:>9.2?} prover={p:>10.2?} verifier={vt:>10.2?} proof={b:>8}B verdict={vd}",
                c = r.num_cons,
                v = r.num_vars,
                n = r.nnz,
                s = r.setup,
                p = r.prover,
                vt = r.verifier,
                b = r.proof_bytes,
                vd = if r.passed { "PASS" } else { "FAIL" },
            );
        }
    }

    if let Some(path) = args.csv {
        emit_csv(&path, &rows);
    }
}

fn run_nizk(
    m: u32,
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    inst: &Instance,
    vars: &libspartan::VarsAssignment,
    inputs: &libspartan::InputsAssignment,
) -> Row {
    let setup_start = Instant::now();
    let gens = NIZKGens::new(num_cons, num_vars, num_inputs);
    let setup = setup_start.elapsed();

    let mut prover_transcript = Transcript::new(b"nizk_example");
    let prover_start = Instant::now();
    let proof = NIZK::prove(inst, vars.clone(), inputs, &gens, &mut prover_transcript);
    let prover = prover_start.elapsed();

    let proof_bytes = bincode::serialize(&proof).expect("encode proof").len();

    let mut verifier_transcript = Transcript::new(b"nizk_example");
    let verifier_start = Instant::now();
    let passed = proof
        .verify(inst, inputs, &mut verifier_transcript, &gens)
        .is_ok();
    let verifier = verifier_start.elapsed();

    Row {
        variant: "NIZK",
        m,
        num_cons,
        num_vars,
        num_inputs,
        nnz: 0,
        setup,
        prover,
        verifier,
        proof_bytes,
        passed,
    }
}

#[allow(clippy::too_many_arguments)]
fn run_snark(
    m: u32,
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    nnz: usize,
    inst: &Instance,
    vars: libspartan::VarsAssignment,
    inputs: &libspartan::InputsAssignment,
) -> Row {
    let setup_start = Instant::now();
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, nnz);
    let (comm, decomm) = SNARK::encode(inst, &gens);
    let setup = setup_start.elapsed();

    let mut prover_transcript = Transcript::new(b"snark_example");
    let prover_start = Instant::now();
    let proof = SNARK::prove(
        inst,
        &comm,
        &decomm,
        vars,
        inputs,
        &gens,
        &mut prover_transcript,
    );
    let prover = prover_start.elapsed();

    let proof_bytes = bincode::serialize(&proof).expect("encode proof").len();

    let mut verifier_transcript = Transcript::new(b"snark_example");
    let verifier_start = Instant::now();
    let passed = proof
        .verify(&comm, inputs, &mut verifier_transcript, &gens)
        .is_ok();
    let verifier = verifier_start.elapsed();

    Row {
        variant: "SNARK",
        m,
        num_cons,
        num_vars,
        num_inputs,
        nnz,
        setup,
        prover,
        verifier,
        proof_bytes,
        passed,
    }
}

fn emit_csv(path: &str, rows: &[Row]) {
    let header = "variant,m,num_constraints,num_vars,num_inputs,nnz,setup_ms,prover_ms,verifier_ms,proof_bytes,passed\n";
    if path == "-" {
        print!("{header}");
        for r in rows {
            println!(
                "{var},{m},{c},{v},{i},{n},{s:.3},{p:.3},{vt:.3},{b},{ok}",
                var = r.variant,
                m = r.m,
                c = r.num_cons,
                v = r.num_vars,
                i = r.num_inputs,
                n = r.nnz,
                s = r.setup.as_secs_f64() * 1000.0,
                p = r.prover.as_secs_f64() * 1000.0,
                vt = r.verifier.as_secs_f64() * 1000.0,
                b = r.proof_bytes,
                ok = r.passed,
            );
        }
    } else {
        let need_header = !Path::new(path).exists();
        let mut f = OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .expect("opening csv");
        if need_header {
            f.write_all(header.as_bytes()).expect("write header");
        }
        for r in rows {
            writeln!(
                f,
                "{var},{m},{c},{v},{i},{n},{s:.3},{p:.3},{vt:.3},{b},{ok}",
                var = r.variant,
                m = r.m,
                c = r.num_cons,
                v = r.num_vars,
                i = r.num_inputs,
                n = r.nnz,
                s = r.setup.as_secs_f64() * 1000.0,
                p = r.prover.as_secs_f64() * 1000.0,
                vt = r.verifier.as_secs_f64() * 1000.0,
                b = r.proof_bytes,
                ok = r.passed,
            )
            .expect("write row");
        }
    }
}
