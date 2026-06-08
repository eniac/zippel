//! Runs every benchmark (schnorr, sumcheck, ipa, kzg, pari) at the rayon
//! thread count of the current process and writes a single CSV.
//!
//! Columns: system, threads, log_size, prover_time_ms, verifier_time_ms,
//!          native_prover_time_ms, native_verifier_time_ms
//!
//! `log_size` is log_2 of the natural complexity parameter (so rows plot
//! linearly on a log-size x-axis):
//!   schnorr  : 0           (no size knob — single fixed protocol)
//!   sumcheck : num_vars    (poly is base(x)^d on the boolean hypercube of dim 2^nv)
//!   ipa      : S           (folding vector length N = 2^S)
//!   kzg      : log_2(N)    (N = coefficient count; degree = N-1)
//!   pari     : M           (K = 2^M constraints)
//!   groth16  : log_2(C)    (C = num_constraints in the bench circuit)
//!
//! Thread sweeping is done by running this binary multiple times with
//! different `RAYON_NUM_THREADS`. The wrapper script `run_all.sh` does that
//! and concatenates the CSVs. We tried `rayon::ThreadPool::install` to vary
//! threads in-process, but arkworks' `parallel` feature hangs on a
//! single-thread pool installed mid-process — running with the global pool
//! sized by `RAYON_NUM_THREADS` is the reliable path.

use benchmarks::{Timing, groth16, hyrax, ipa, kzg, pari, pst13, schnorr, spartan, sumcheck};
use clap::Parser;
use libspartan::{Instance, NIZK, NIZKGens};
use merlin::Transcript;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

const ALL_SYSTEMS: &[&str] = &[
    "schnorr", "sumcheck", "ipa", "kzg", "pari", "groth16", "pst13", "hyrax", "spartan",
];

#[derive(Parser, Debug)]
#[command(about = "Run every benchmark at the current rayon thread count and emit a CSV")]
struct Args {
    /// Output CSV path.
    #[arg(long, default_value = "bench_results.csv")]
    out: PathBuf,
    /// Comma-separated subset of systems to run (default: all).
    #[arg(long, value_delimiter = ',')]
    systems: Option<Vec<String>>,
    /// Use a smaller, faster size grid for iteration.
    #[arg(long)]
    quick: bool,
    /// Override the `threads` column. Useful when the wrapper script
    /// pinned a thread count via `RAYON_NUM_THREADS` but the rayon pool
    /// reports something different (rarely needed).
    #[arg(long)]
    threads_label: Option<usize>,
    /// Don't write the CSV header row (for concatenating across runs).
    #[arg(long)]
    no_header: bool,
}

struct Row {
    system: &'static str,
    threads: usize,
    log_size: usize,
    zippel: Timing,
    native: Timing,
}

fn ms(t: std::time::Duration) -> f64 {
    t.as_secs_f64() * 1000.0
}

fn write_csv(path: &PathBuf, rows: &[Row], header: bool) -> std::io::Result<()> {
    let f = File::create(path)?;
    let mut w = BufWriter::new(f);
    if header {
        writeln!(
            w,
            "system,threads,log_size,prover_time_ms,verifier_time_ms,native_prover_time_ms,native_verifier_time_ms"
        )?;
    }
    for r in rows {
        writeln!(
            w,
            "{},{},{},{:.3},{:.3},{:.3},{:.3}",
            r.system,
            r.threads,
            r.log_size,
            ms(r.zippel.prove),
            ms(r.zippel.verify),
            ms(r.native.prove),
            ms(r.native.verify),
        )?;
    }
    w.flush()
}

fn print_row(r: &Row) {
    eprintln!(
        "  {:<8} threads={} log_size={:>2}  prove={:>8.2}ms / native {:>8.2}ms   verify={:>7.2}ms / native {:>7.2}ms",
        r.system,
        r.threads,
        r.log_size,
        ms(r.zippel.prove),
        ms(r.native.prove),
        ms(r.zippel.verify),
        ms(r.native.verify),
    );
}

fn run_schnorr(threads: usize) -> Vec<Row> {
    let mut z = schnorr::zippel_side::Setup::new();
    let n = schnorr::native_side::Setup::new();
    let zippel = z.time_protocol();
    let native = n.time_protocol();
    // Schnorr has no size knob — log_size = 0 marks "single fixed point".
    vec![Row {
        system: "schnorr",
        threads,
        log_size: 0,
        zippel,
        native,
    }]
}

fn run_sumcheck(threads: usize, sizes: &[usize], max_degree: usize) -> Vec<Row> {
    sizes
        .iter()
        .map(|&nv| {
            let mut z = sumcheck::zippel_side::Setup::new(nv, max_degree);
            let n = sumcheck::native_side::Setup::new(nv, max_degree);
            let zippel = z.time_protocol();
            let native = n.time_protocol();
            // Sumcheck size knob is `num_vars` itself — the hypercube has 2^nv
            // points, so num_vars is already log_2 of the domain size.
            let r = Row {
                system: "sumcheck",
                threads,
                log_size: nv,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_ipa(threads: usize, ss: &[usize]) -> Vec<Row> {
    ss.iter()
        .map(|&s| {
            let mut z = ipa::zippel_side::Setup::new(s);
            let n = ipa::native_side::Setup::new(s);
            let zippel = z.time_protocol();
            let native = n.time_protocol();
            let r = Row {
                system: "ipa",
                threads,
                log_size: s,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_kzg(threads: usize, ns: &[usize]) -> Vec<Row> {
    ns.iter()
        .map(|&n_coeffs| {
            let mut z = kzg::zippel_side::Setup::new(n_coeffs);
            let n = kzg::native_side::Setup::new(n_coeffs);
            let zippel = z.time_protocol();
            let native = n.time_protocol();
            // KZG's grid is restricted to powers of two so log_2 is exact;
            // `trailing_zeros` is the cheap path for that.
            let r = Row {
                system: "kzg",
                threads,
                log_size: n_coeffs.trailing_zeros() as usize,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_pari(threads: usize, ms: &[usize], n_pub: usize, k_vars: usize) -> Vec<Row> {
    ms.iter()
        .map(|&m_log| {
            let m_witness = k_vars.saturating_sub(2 * n_pub);
            let mut rng = ark_std::test_rng();
            let inst = pari::inst_gen::build_random(m_log, n_pub, m_witness, &mut rng);
            let mut z = pari::zippel_side::Setup::new(m_log, n_pub, inst.num_vars);
            let n = pari::native_side::Setup::new(&inst);
            let zippel = z.time_protocol(&inst);
            let native = n.time_protocol(&inst);
            let r = Row {
                system: "pari",
                threads,
                log_size: m_log,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_groth16(threads: usize, log_sizes: &[usize]) -> Vec<Row> {
    log_sizes
        .iter()
        .map(|&log_size| {
            let num_constraints = 1usize << log_size;
            let translated = groth16::build_translated(num_constraints);
            let mut z = groth16::zippel_side::Setup::new(&translated);
            let n = groth16::native_side::Setup::new(&translated);
            let zippel = z.time_protocol();
            let native = n.time_protocol();
            let r = Row {
                system: "groth16",
                threads,
                log_size,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_pst13(threads: usize, ns: &[usize]) -> Vec<Row> {
    ns.iter()
        .map(|&n| {
            let shared = pst13::shared::build(n);
            let mut z = pst13::zippel_side::Setup::new(&shared);
            let np = pst13::native_side::Setup::new(&shared);
            let zippel = z.time_protocol();
            let native = np.time_protocol();
            let r = Row {
                system: "pst13",
                threads,
                log_size: n,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_hyrax(threads: usize, ns: &[usize]) -> Vec<Row> {
    ns.iter()
        .map(|&n| {
            let mut z = hyrax::zippel_side::Setup::new(n);
            let np = hyrax::native_side::Setup::new(n);
            let zippel = z.time_protocol();
            let native = np.time_protocol();
            let r = Row {
                system: "hyrax",
                threads,
                log_size: n,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_spartan(threads: usize, ms: &[usize]) -> Vec<Row> {
    ms.iter()
        .map(|&m| {
            let mut z = spartan::Setup::new(m);
            let zippel = z.timing();

            let num_cons = 1usize << m;
            let num_vars = 1usize << (m - 1);
            let num_inputs = num_vars - 1;
            let (inst, vars, inputs) =
                Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

            let n_matvec = {
                let mut best = Duration::MAX;
                for _ in 0..3 {
                    let t0 = Instant::now();
                    let sat = inst.is_sat(&vars, &inputs).expect("is_sat");
                    let dt = t0.elapsed();
                    assert!(sat);
                    if dt < best {
                        best = dt;
                    }
                }
                best
            };

            let gens = NIZKGens::new(num_cons, num_vars, num_inputs);
            let inst_bytes = vec![0u8; 3 * num_cons * 40];
            let inputs_bytes = bincode::serialize(&inputs).expect("serialize inputs");

            let mut pt = Transcript::new(b"bench_all_spartan");
            let t = Instant::now();
            {
                let mut bind = Transcript::new(b"matrix_bind");
                bind.append_message(b"inst", &inst_bytes);
                bind.append_message(b"io", &inputs_bytes);
            }
            let proof = NIZK::prove(&inst, vars.clone(), &inputs, &gens, &mut pt);
            let native_prove = t.elapsed().saturating_sub(n_matvec);

            let mut vt = Transcript::new(b"bench_all_spartan");
            let t = Instant::now();
            {
                let mut bind = Transcript::new(b"matrix_bind");
                bind.append_message(b"inst", &inst_bytes);
                bind.append_message(b"io", &inputs_bytes);
            }
            proof.verify(&inst, &inputs, &mut vt, &gens).expect("verify");
            let native_verify = t.elapsed();

            let native = Timing {
                prove: native_prove,
                verify: native_verify,
            };
            let r = Row {
                system: "spartan",
                threads,
                log_size: m,
                zippel,
                native,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn main() {
    let args = Args::parse();
    let selected: Vec<&'static str> = match &args.systems {
        Some(names) => ALL_SYSTEMS
            .iter()
            .copied()
            .filter(|s| names.iter().any(|n| n == s))
            .collect(),
        None => ALL_SYSTEMS.to_vec(),
    };

    let threads = args
        .threads_label
        .unwrap_or_else(rayon::current_num_threads);

    // Default grid: log_size = 1..=20 for systems whose cost scales gracefully
    // (sumcheck/pari/kzg are FFT-dominated, ~K log K). IPA is capped at 14
    // because its prover + verifier are O(N) MSMs — at S=20 (N=2^20 ≈ 1M)
    // single-threaded runs push into many minutes per call.
    // Default grid: log_size = 1..=20 for systems whose cost scales gracefully
    // (sumcheck/pari/kzg are FFT-dominated, ~K log K). IPA is capped at 14
    // because its prover + verifier are O(N) MSMs — at S=20 (N=2^20 ≈ 1M)
    // single-threaded runs push into many minutes per call.
    //
    // Sumcheck starts at nv=3 because sumcheck.zippel's `V: 2..NUM_VARS_CONST`
    // range must be non-empty (V is the per-round residual var count).
    //
    // PARI starts at M=2 because the protocol divides q(X) by (X−r); at
    // K=2 the quotient q has degree 0 and the type checker rejects the
    // div. K=4 (M=2) is the smallest size where q has degree ≥ 1.
    // Groth16 sweep is capped at log_constraints=14 (16K constraints).
    // Beyond that, the zippel-side keys + circuit balloon (a_query,
    // b_query, h_query are each Vec<G1Projective> of length ≥
    // num_constraints), and single-thread prove already runs in
    // tens of seconds at log_size=14.
    let (pari_ms, sumcheck_nvs, ipa_ss, kzg_ns, groth16_log_ns, pst13_ns, hyrax_ns, spartan_ms) =
        if args.quick {
            (
                vec![4usize, 8],
                vec![4usize, 8],
                vec![4usize, 6],
                vec![16usize, 256],
                vec![4usize, 8],
                vec![4usize, 8],
                vec![4usize, 8],
                vec![4usize, 8],
            )
        } else {
            (
                (2..=20).collect::<Vec<_>>(),
                (3..=20).collect::<Vec<_>>(),
                (1..=14).collect::<Vec<_>>(),
                (1..=20).map(|s| 1usize << s).collect::<Vec<_>>(),
                (1..=14).collect::<Vec<_>>(),
                (1..=20).collect::<Vec<_>>(),
                (2..=20).step_by(2).collect::<Vec<_>>(),
                (3..=20).collect::<Vec<_>>(),
            )
        };
    // Sumcheck max_degree=3 matches the default the existing sumcheck bench uses;
    // pari n_pub=1 / k_vars=3 mirrors the sweep we've been running by hand.
    let sumcheck_degree = 3usize;
    let pari_n_pub = 1usize;
    let pari_k_vars = 3usize;

    eprintln!("=== bench_all ===");
    eprintln!("systems : {:?}", selected);
    eprintln!("threads : {} (RAYON_NUM_THREADS or default)", threads);
    eprintln!("out     : {}", args.out.display());
    eprintln!();

    let mut all_rows: Vec<Row> = Vec::new();
    let started = Instant::now();

    for &sys in &selected {
        let chunk = match sys {
            "schnorr" => {
                let r = run_schnorr(threads);
                for row in &r {
                    print_row(row);
                }
                r
            }
            "sumcheck" => run_sumcheck(threads, &sumcheck_nvs, sumcheck_degree),
            "ipa" => run_ipa(threads, &ipa_ss),
            "kzg" => run_kzg(threads, &kzg_ns),
            "pari" => run_pari(threads, &pari_ms, pari_n_pub, pari_k_vars),
            "groth16" => run_groth16(threads, &groth16_log_ns),
            "pst13" => run_pst13(threads, &pst13_ns),
            "hyrax" => run_hyrax(threads, &hyrax_ns),
            "spartan" => run_spartan(threads, &spartan_ms),
            other => panic!("unknown system: {other}"),
        };
        all_rows.extend(chunk);
    }

    write_csv(&args.out, &all_rows, !args.no_header).expect("write csv");
    eprintln!();
    eprintln!(
        "wrote {} rows to {} in {:.1}s",
        all_rows.len(),
        args.out.display(),
        started.elapsed().as_secs_f64(),
    );
}
