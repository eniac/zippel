//! Runs every benchmark (schnorr, sumcheck, ipa, kzg, pari, groth16, pst13, hyrax, spartan) at the rayon
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
//!   pst13    : log_2(N)    (N = coefficient count)
//!   hyrax    : log_size    (n = total multilinear variables)
//!   spartan  : M           (num_constraints = 2^M)
//!
//! Thread sweeping is done by running this binary multiple times with
//! different `RAYON_NUM_THREADS`. The wrapper script `run_sweep.sh` does that
//! and concatenates the CSVs. We tried `rayon::ThreadPool::install` to vary
//! threads in-process, but arkworks' `parallel` feature hangs on a
//! single-thread pool installed mid-process — running with the global pool
//! sized by `RAYON_NUM_THREADS` is the reliable path.

use benchmarks::{Timing, groth16, hyrax, ipa, kzg, pari, pst13, schnorr, spartan, sumcheck};
use clap::Parser;
use libspartan::{Instance, NIZK, NIZKGens};
use merlin::Transcript;
use std::fs::OpenOptions;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};
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
    /// Append to the output CSV instead of truncating it. Pair with
    /// `--no-header` when continuing a file written by an earlier run
    /// (e.g. `run_all.sh` sweeping multiple thread counts into a single
    /// CSV — each thread iteration appends so Ctrl-C never loses rows).
    #[arg(long)]
    append: bool,
    /// Override every system's log_size grid with this comma-separated
    /// list. For kzg the entries are converted to n_coeffs = 1 << log_size.
    /// Useful for re-running a single failing point, e.g.
    /// `--systems spartan --sizes 7`.
    #[arg(long, value_delimiter = ',')]
    sizes: Option<Vec<usize>>,
}

struct Row {
    system: &'static str,
    threads: usize,
    log_size: usize,
    zippel: Timing,
    native: Timing,
    /// Wall-clock time for the zippel compiler: source → executable
    /// graph (parse + type-check + graph construction inside
    /// `ZippelHandler::compile`). Excludes the Rust compiler (which
    /// builds this binary once), excludes runtime scheduling
    /// (graph→TDag), and excludes prove/verify execution.
    compile: std::time::Duration,
    /// Optional second native baseline for the same system. Populated
    /// today only for spartan: `native` holds Microsoft's `libspartan`
    /// (curve25519-dalek stack), `ark_native` holds the vendored
    /// ark-spartan on ark-curve25519 0.6 — the same curve zippel runs
    /// on. Two natives so the reader can attribute the gap to (a)
    /// implementation quality (libspartan vs zippel-generated code)
    /// vs (b) library-stack cost (dalek vs arkworks 0.6). `None` for
    /// every other system.
    ark_native: Option<Timing>,
}

fn ms(t: std::time::Duration) -> f64 {
    t.as_secs_f64() * 1000.0
}

const ZIPPEL_SCHNORR: &str = include_str!("../../../examples/schnorr/schnorr.zippel");
const ZIPPEL_SUMCHECK: &str = include_str!("../../../examples/sumcheck/sumcheck.zippel");
const ZIPPEL_IPA: &str = include_str!("../../../examples/ipa/ipa.zippel");
const ZIPPEL_KZG: &str = include_str!("../../../examples/kzg/kzg.zippel");
const ZIPPEL_PARI: &str = include_str!("../../../examples/pari/pari.zippel");
const ZIPPEL_GROTH16: &str = include_str!("../../../examples/groth16/groth16.zippel");
const ZIPPEL_PST13: &str = include_str!("../../../examples/pst13/pst13.zippel");
const ZIPPEL_HYRAX: &str = include_str!("../../../examples/hyrax/hyrax.zippel");
const ZIPPEL_SPARTAN: &str = include_str!("../../../examples/spartan/spartan.zippel");

const NATIVE_IPA_RS: &str = include_str!("../../src/ipa.rs");
// Upstream PARI baseline: vendored from alireza-shirzad/garuda-pari (commit
// 3db79ad). NCLOC sums prover + verifier + generator + data_structures +
// utils + the bit of `shared-utils` Pari actually uses (the transcript and
// two inlined helpers in pari_upstream/mod.rs).
const NATIVE_PARI_MOD_RS: &str = include_str!("../../src/pari_upstream/mod.rs");
const NATIVE_PARI_GEN_RS: &str = include_str!("../../src/pari_upstream/generator.rs");
const NATIVE_PARI_PROVER_RS: &str = include_str!("../../src/pari_upstream/prover.rs");
const NATIVE_PARI_VERIFIER_RS: &str = include_str!("../../src/pari_upstream/verifier.rs");
const NATIVE_PARI_DS_RS: &str = include_str!("../../src/pari_upstream/data_structures.rs");
const NATIVE_PARI_UTILS_RS: &str = include_str!("../../src/pari_upstream/utils.rs");
const NATIVE_PARI_TRANSCRIPT_RS: &str = include_str!("../../src/pari_upstream/transcript/mod.rs");
const NATIVE_PARI_TRANSCRIPT_ERR_RS: &str =
    include_str!("../../src/pari_upstream/transcript/errors.rs");

// PST13 native baseline is vendored + patched (see src/pst13_upstream/).
// NCLOC counts mod.rs + data_structures.rs of our vendored version,
// reflecting what code actually runs in the bench.
const NATIVE_PST13_MOD_RS: &str = include_str!("../../src/pst13_upstream/mod.rs");
const NATIVE_PST13_DS_RS: &str = include_str!("../../src/pst13_upstream/data_structures.rs");

// Hyrax native baseline is vendored + patched (see src/hyrax_upstream/).
// Replaces upstream `Matrix<F>` (Vec<Vec<F>>) with flat row-major
// storage and rewrites `row_mul` as a SAXPY accumulation — eliminates
// the per-column 16KB temp Vec and the cache-hostile column gathers.
const NATIVE_HYRAX_MOD_RS: &str = include_str!("../../src/hyrax_upstream/mod.rs");

// For systems delegating to external crates, native = prover + verifier code
// in the underlying crate (counted once locally with `cloc`-style NCLOC, pinned
// to the version in benchmarks/Cargo.lock at the time these were measured).
const SCHNORR_EXT_NCLOC: usize = 186; // ark-crypto-primitives-0.6.0 src/signature/schnorr/mod.rs
const SUMCHECK_EXT_NCLOC: usize = 1544; // vendored from hyperplonk: src/sumcheck_upstream/{arithmetic,poly_iop,transcript}/*.rs (ported to ark 0.6)
const KZG_EXT_NCLOC: usize = 527; // ark-poly-commit-0.6.0 src/kzg10/mod.rs
const GROTH16_EXT_NCLOC: usize = 458; // ark-groth16-0.6.0 src/{prover,verifier,r1cs_to_qap}.rs
const SPARTAN_EXT_NCLOC: usize = 1867; // spartan-0.9.0 src/{r1csproof,sumcheck}.rs + src/nizk/{mod,bullet}.rs
// PST13, Hyrax, PARI, and IPA native NCLOC are computed dynamically from their
// respective source files above.

fn count_ncloc_line_comments(src: &str) -> usize {
    src.lines()
        .filter(|l| {
            let t = l.trim();
            !t.is_empty() && !t.starts_with("//")
        })
        .count()
}

fn count_ncloc_rust(src: &str) -> usize {
    let mut count = 0usize;
    let mut in_block = false;
    for line in src.lines() {
        let trimmed = line.trim();
        if in_block {
            if let Some(after) = trimmed.split_once("*/") {
                in_block = false;
                let rest = after.1.trim();
                if !rest.is_empty() && !rest.starts_with("//") {
                    count += 1;
                }
            }
            continue;
        }
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }
        if trimmed.starts_with("/*") && !trimmed.contains("*/") {
            in_block = true;
            continue;
        }
        count += 1;
    }
    count
}

fn extract_braced_block<'a>(src: &'a str, header: &str) -> &'a str {
    let Some(start) = src.find(header) else {
        return "";
    };
    let after = &src[start..];
    let Some(brace) = after.find('{') else {
        return "";
    };
    let mut depth: i32 = 1;
    let body = &after[brace + 1..];
    for (i, c) in body.char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return &body[..i];
                }
            }
            _ => {}
        }
    }
    body
}

fn zippel_ncloc(sys: &str) -> usize {
    match sys {
        "schnorr" => count_ncloc_line_comments(ZIPPEL_SCHNORR),
        "sumcheck" => count_ncloc_line_comments(ZIPPEL_SUMCHECK),
        "ipa" => count_ncloc_line_comments(ZIPPEL_IPA),
        "kzg" => count_ncloc_line_comments(ZIPPEL_KZG),
        "pari" => count_ncloc_line_comments(ZIPPEL_PARI),
        "groth16" => count_ncloc_line_comments(ZIPPEL_GROTH16),
        "pst13" => count_ncloc_line_comments(ZIPPEL_PST13),
        "hyrax" => count_ncloc_line_comments(ZIPPEL_HYRAX),
        "spartan" => count_ncloc_line_comments(ZIPPEL_SPARTAN),
        _ => 0,
    }
}

fn native_ncloc(sys: &str) -> usize {
    match sys {
        "schnorr" => SCHNORR_EXT_NCLOC,
        "sumcheck" => SUMCHECK_EXT_NCLOC,
        "kzg" => KZG_EXT_NCLOC,
        "groth16" => GROTH16_EXT_NCLOC,
        "pst13" => count_ncloc_rust(NATIVE_PST13_MOD_RS) + count_ncloc_rust(NATIVE_PST13_DS_RS),
        "spartan" => SPARTAN_EXT_NCLOC,
        "ipa" => count_ncloc_rust(extract_braced_block(NATIVE_IPA_RS, "pub mod native_side")),
        "hyrax" => count_ncloc_rust(NATIVE_HYRAX_MOD_RS),
        "pari" => {
            count_ncloc_rust(NATIVE_PARI_MOD_RS)
                + count_ncloc_rust(NATIVE_PARI_GEN_RS)
                + count_ncloc_rust(NATIVE_PARI_PROVER_RS)
                + count_ncloc_rust(NATIVE_PARI_VERIFIER_RS)
                + count_ncloc_rust(NATIVE_PARI_DS_RS)
                + count_ncloc_rust(NATIVE_PARI_UTILS_RS)
                + count_ncloc_rust(NATIVE_PARI_TRANSCRIPT_RS)
                + count_ncloc_rust(NATIVE_PARI_TRANSCRIPT_ERR_RS)
        }
        _ => 0,
    }
}

static CSV_WRITER: OnceLock<Mutex<BufWriter<std::fs::File>>> = OnceLock::new();

fn init_csv(path: &PathBuf, header: bool, append: bool) -> std::io::Result<()> {
    // Truncate UNLESS the caller asked to append. `header` is independent:
    // run_all.sh writes the header on the first thread iteration (header=true,
    // append=false → truncate + write header) and then appends headerless rows
    // for subsequent threads (header=false, append=true → keep existing rows).
    if !append {
        std::fs::write(path, "")?;
    }
    let f = OpenOptions::new().create(true).append(true).open(path)?;
    let mut w = BufWriter::new(f);
    if header {
        // ark_native_prover_time_ms / ark_native_verifier_time_ms are
        // populated only for the spartan row (the ark-spartan baseline
        // on ark-curve25519 v0.6). Blank for every other system.
        writeln!(
            w,
            "system,threads,log_size,prover_time_ms,verifier_time_ms,native_prover_time_ms,native_verifier_time_ms,zippel_ncloc,native_ncloc,compiler,ark_native_prover_time_ms,ark_native_verifier_time_ms"
        )?;
        w.flush()?;
    }
    CSV_WRITER
        .set(Mutex::new(w))
        .map_err(|_| std::io::Error::other("CSV_WRITER already initialized"))
}

fn write_row(r: &Row) {
    let Some(m) = CSV_WRITER.get() else { return };
    let mut w = m.lock().unwrap();
    // ark_native columns: 6-decimal ms if present, empty string otherwise.
    let (ark_prove, ark_verify) = match r.ark_native {
        Some(t) => (format!("{:.3}", ms(t.prove)), format!("{:.3}", ms(t.verify))),
        None => (String::new(), String::new()),
    };
    writeln!(
        w,
        "{},{},{},{:.3},{:.3},{:.3},{:.3},{},{},{:.3},{},{}",
        r.system,
        r.threads,
        r.log_size,
        ms(r.zippel.prove),
        ms(r.zippel.verify),
        ms(r.native.prove),
        ms(r.native.verify),
        zippel_ncloc(r.system),
        native_ncloc(r.system),
        ms(r.compile),
        ark_prove,
        ark_verify,
    )
    .expect("write csv row");
    w.flush().expect("flush csv row");
}

fn print_row(r: &Row) {
    eprintln!(
        "  {:<8} threads={} log_size={:>2}  prove={:>8.2}ms / native {:>8.2}ms   verify={:>7.2}ms / native {:>7.2}ms   compile={:>8.2}ms",
        r.system,
        r.threads,
        r.log_size,
        ms(r.zippel.prove),
        ms(r.native.prove),
        ms(r.zippel.verify),
        ms(r.native.verify),
        ms(r.compile),
    );
    if let Some(t) = r.ark_native {
        eprintln!(
            "  {:<8} threads={} log_size={:>2}  ark_native prove={:>8.2}ms   verify={:>7.2}ms   (ark-spartan on ark-curve25519 0.6)",
            r.system,
            r.threads,
            r.log_size,
            ms(t.prove),
            ms(t.verify),
        );
    }
    write_row(r);
}

fn run_schnorr(threads: usize) -> Vec<Row> {
    let (mut z, n) = setup_pool().install(|| {
        (
            schnorr::zippel_side::Setup::new(),
            schnorr::native_side::Setup::new(),
        )
    });
    let compile = z.compile_time();
    let zippel = z.time_protocol();
    let native = n.time_protocol();
    // Schnorr has no size knob — log_size = 0 marks "single fixed point".
    vec![Row {
        system: "schnorr",
        threads,
        log_size: 0,
        zippel,
        native,
        compile,
        ark_native: None,
    }]
}

fn run_sumcheck(threads: usize, sizes: &[usize], max_degree: usize) -> Vec<Row> {
    sizes
        .iter()
        .map(|&nv| {
            let (mut z, n) = setup_pool().install(|| {
                (
                    sumcheck::zippel_side::Setup::new(nv, max_degree),
                    sumcheck::native_side::Setup::new(nv, max_degree),
                )
            });
            let compile = z.compile_time();
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
                compile,
                ark_native: None,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_ipa(threads: usize, ss: &[usize]) -> Vec<Row> {
    ss.iter()
        .map(|&s| {
            let (mut z, n) = setup_pool().install(|| {
                (
                    ipa::zippel_side::Setup::new(s),
                    ipa::native_side::Setup::new(s),
                )
            });
            let compile = z.compile_time();
            let zippel = z.time_protocol();
            let native = n.time_protocol();
            let r = Row {
                system: "ipa",
                threads,
                log_size: s,
                zippel,
                native,
                compile,
                ark_native: None,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_kzg(threads: usize, ns: &[usize]) -> Vec<Row> {
    ns.iter()
        .map(|&n_coeffs| {
            let (mut z, n) = setup_pool().install(|| {
                (
                    kzg::zippel_side::Setup::new(n_coeffs),
                    kzg::native_side::Setup::new(n_coeffs),
                )
            });
            let compile = z.compile_time();
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
                compile,
                ark_native: None,
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
            let (inst, mut z, n) = setup_pool().install(|| {
                let mut rng = ark_std::test_rng();
                let inst = pari::inst_gen::build_random(m_log, n_pub, m_witness, &mut rng);
                let z = pari::zippel_side::Setup::new(m_log, n_pub, &inst);
                let n = pari::native_side::Setup::new(&inst);
                (inst, z, n)
            });
            let compile = z.compile_time();
            let zippel = z.time_protocol(&inst);
            let native = n.time_protocol(&inst);
            let r = Row {
                system: "pari",
                threads,
                log_size: m_log,
                zippel,
                native,
                compile,
                ark_native: None,
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
            // `translated` borrowed by both setups, so build all three
            // inside the same install closure and pass them out as a
            // tuple. `translated` outlives both setups for the duration
            // of `time_protocol`, which is what the borrow requires.
            let translated = setup_pool().install(|| {
                benchmarks::cache::load_or_build_canonical("groth16_translated", log_size, || {
                    groth16::build_translated(num_constraints)
                })
            });
            let (mut z, n) = setup_pool().install(|| {
                (
                    groth16::zippel_side::Setup::new(&translated),
                    groth16::native_side::Setup::new(&translated),
                )
            });
            let compile = z.compile_time();
            let zippel = z.time_protocol();
            let native = n.time_protocol();
            let r = Row {
                system: "groth16",
                threads,
                log_size,
                zippel,
                native,
                compile,
                ark_native: None,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_pst13(threads: usize, ns: &[usize]) -> Vec<Row> {
    ns.iter()
        .map(|&n| {
            let shared = setup_pool().install(|| pst13::shared::build(n));
            let (mut z, np) = setup_pool().install(|| {
                (
                    pst13::zippel_side::Setup::new(&shared),
                    pst13::native_side::Setup::new(&shared),
                )
            });
            let compile = z.compile_time();
            let zippel = z.time_protocol();
            let native = np.time_protocol();
            let r = Row {
                system: "pst13",
                threads,
                log_size: n,
                zippel,
                native,
                compile,
                ark_native: None,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_hyrax(threads: usize, ns: &[usize]) -> Vec<Row> {
    ns.iter()
        .map(|&n| {
            let (mut z, np) = setup_pool().install(|| {
                (
                    hyrax::zippel_side::Setup::new(n),
                    hyrax::native_side::Setup::new(n),
                )
            });
            let compile = z.compile_time();
            let zippel = z.time_protocol();
            let native = np.time_protocol();
            let r = Row {
                system: "hyrax",
                threads,
                log_size: n,
                zippel,
                native,
                compile,
                ark_native: None,
            };
            print_row(&r);
            r
        })
        .collect()
}

fn run_spartan(threads: usize, ms: &[usize]) -> Vec<Row> {
    ms.iter()
        .map(|&m| {
            let mut z = setup_pool().install(|| spartan::Setup::new(m));
            let compile = z.compile_time();
            // `z.timing()` IS the timed region for the zippel side —
            // it runs run_prover + run_verifier internally, so we hand
            // it to the global (bench) pool, not the setup pool.
            let zippel = z.timing();

            let num_cons = 1usize << m;
            let num_vars = 1usize << (m - 1);
            let num_inputs = num_vars - 1;
            // Synthesize the R1CS instance + gens off the bench pool.
            // `produce_synthetic_r1cs` + `NIZKGens::new` are pure setup
            // (libspartan with the multicore feature uses rayon, so the
            // install routes them onto every core).
            let (inst, vars, inputs, gens, inst_bytes, inputs_bytes, n_matvec) = setup_pool()
                .install(|| {
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
                    (inst, vars, inputs, gens, inst_bytes, inputs_bytes, n_matvec)
                });

            // Prover sampled PROVER_SAMPLES times. Each iteration
            // re-inits the transcript (NIZK::prove takes &mut and consumes it).
            let mut prove_sum = Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*benchmarks::PROVER_SAMPLES {
                let mut pt = Transcript::new(b"bench_all_spartan");
                let t = Instant::now();
                {
                    let mut bind = Transcript::new(b"matrix_bind");
                    bind.append_message(b"inst", &inst_bytes);
                    bind.append_message(b"io", &inputs_bytes);
                }
                let proof = NIZK::prove(&inst, vars.clone(), &inputs, &gens, &mut pt);
                prove_sum += t.elapsed().saturating_sub(n_matvec);
                last_proof = Some(proof);
            }
            let native_prove = prove_sum / *benchmarks::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            // Verifier sampled VERIFY_SAMPLES times. Transcript
            // construction is the same trivial work the original timer
            // included (mirrors the prover-side measurement), so we keep
            // it inside the per-call timer. libspartan's verify takes
            // &mut transcript, so it must be re-init per iteration.
            let mut verify_sum = Duration::ZERO;
            for _ in 0..benchmarks::VERIFY_SAMPLES {
                let mut vt = Transcript::new(b"bench_all_spartan");
                let t = Instant::now();
                {
                    let mut bind = Transcript::new(b"matrix_bind");
                    bind.append_message(b"inst", &inst_bytes);
                    bind.append_message(b"io", &inputs_bytes);
                }
                proof
                    .verify(&inst, &inputs, &mut vt, &gens)
                    .expect("verify");
                verify_sum += t.elapsed();
            }
            let native_verify = verify_sum / benchmarks::VERIFY_SAMPLES;

            let native = Timing {
                prove: native_prove,
                verify: native_verify,
            };

            // Second native baseline: ark-spartan on ark-curve25519 v0.6
            // (same curve as the zippel side; different arkworks stack
            // than libspartan, which lives on curve25519-dalek). Setup
            // (R1CS synthesis + gens) runs off the bench pool, then the
            // prover/verifier are timed in the global pool the same way
            // as libspartan above.
            let ark_native = {
                use ark_curve25519::EdwardsProjective as C25519;
                use benchmarks::ark_spartan_upstream::{
                    Instance as ArkInstance, NIZK as ArkNIZK, NIZKGens as ArkNIZKGens,
                };

                let (ark_inst, ark_vars, ark_inputs, ark_gens) = setup_pool().install(|| {
                    let (ark_inst, ark_vars, ark_inputs) =
                        ArkInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
                    let ark_gens =
                        ArkNIZKGens::<C25519>::new(num_cons, num_vars, num_inputs);
                    (ark_inst, ark_vars, ark_inputs, ark_gens)
                });

                let mut prove_sum = Duration::ZERO;
                let mut last_ark_proof = None;
                for _ in 0..*benchmarks::PROVER_SAMPLES {
                    let mut pt = Transcript::new(b"bench_all_spartan_ark");
                    let t = Instant::now();
                    let proof =
                        ArkNIZK::<C25519>::prove(&ark_inst, ark_vars.clone(), &ark_inputs, &ark_gens, &mut pt);
                    prove_sum += t.elapsed();
                    last_ark_proof = Some(proof);
                }
                let ark_prove = prove_sum / *benchmarks::PROVER_SAMPLES;
                let proof = last_ark_proof.expect("PROVER_SAMPLES > 0");

                let mut verify_sum = Duration::ZERO;
                for _ in 0..benchmarks::VERIFY_SAMPLES {
                    let mut vt = Transcript::new(b"bench_all_spartan_ark");
                    let t = Instant::now();
                    proof
                        .verify(&ark_inst, &ark_inputs, &mut vt, &ark_gens)
                        .expect("ark-spartan verify");
                    verify_sum += t.elapsed();
                }
                let ark_verify = verify_sum / benchmarks::VERIFY_SAMPLES;

                Some(Timing { prove: ark_prove, verify: ark_verify })
            };

            let r = Row {
                system: "spartan",
                threads,
                log_size: m,
                zippel,
                native,
                compile,
                ark_native,
            };
            print_row(&r);
            r
        })
        .collect()
}

// Separate rayon pool used for the setup/SRS-generation work that runs
// OUTSIDE the timed prove/verify. The global pool is constrained to the
// benchmark thread count (1, 2, 4, 8, 16...) so we can measure scaling,
// but setup is bench-harness overhead — we want it to use every core.
// `setup_pool().install(|| { ... })` routes nested `par_iter`/`join`/`spawn`
// to this all-core pool; control returns to the global pool the moment
// `install` returns, so it can't bleed into a timed region.
static SETUP_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
fn setup_pool() -> &'static rayon::ThreadPool {
    SETUP_POOL.get().expect("SETUP_POOL not initialized")
}

fn main() {
    // Init the rayon global pool with a 64 MB worker stack before any
    // rayon call — the default per-worker stack is the OS default
    // (~2 MB on macOS/Linux), and HyraxPC's open/check at n=20 pushes
    // multi-MB frames through `par_iter` chains and overflows. Must
    // happen before `Args::parse()` (clap) or any other touch of rayon,
    // because `build_global` errors if the pool is already initialized.
    // Honors RAYON_NUM_THREADS the way the implicit pool does.
    let num_threads = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(0); // 0 → rayon picks (= num CPUs)
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .stack_size(64 * 1024 * 1024)
        .build_global()
        .expect("init rayon global pool");

    // Build the all-core SETUP_POOL after the global pool so it can't
    // accidentally be picked up by `build_global`. Uses the same 64 MB
    // worker stack because some setup paths (groth16 keygen, kzg SRS,
    // pari `compute_ai_bi_at_tau`) push the same large frames the
    // timed paths do.
    let setup_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(num_threads.max(1));
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(setup_threads)
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("init rayon setup pool");
    SETUP_POOL
        .set(pool)
        .map_err(|_| ())
        .expect("SETUP_POOL already initialized");

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

    // Default grid: every system at log_size=20 (domain size 2^20 ≈ 1M).
    // sumcheck/pari/kzg/pst13/hyrax/spartan are FFT-dominated (~K log K)
    // and finish in seconds-to-minutes per single-threaded prove. IPA's
    // prover/verifier are O(N) MSMs with no FFT shortcut (log_2(N) folding
    // rounds, each halving the vector), so S=20 single-threaded runs in
    // tens of seconds. Groth16 at log_constraints=20 is the heaviest:
    // a_query/b_query/h_query/l_query are each Vec<G1Projective> of length
    // ≥ num_constraints (~150 MB per vector on BLS12-381 → ~1 GB peak RSS
    // for the keys alone), and single-thread prove runs into many minutes.
    //
    // Sumcheck starts at nv=3 because sumcheck.zippel's `V: 2..NUM_VARS_CONST`
    // range must be non-empty (V is the per-round residual var count).
    //
    // PARI starts at M=2 because the protocol divides q(X) by (X−r); at
    // K=2 the quotient q has degree 0 and the type checker rejects the
    // div. K=4 (M=2) is the smallest size where q has degree ≥ 1.
    let (pari_ms, sumcheck_nvs, ipa_ss, kzg_ns, groth16_log_ns, pst13_ns, hyrax_ns, spartan_ms) =
        if let Some(ls) = &args.sizes {
            let kzg = ls.iter().map(|&s| 1usize << s).collect::<Vec<_>>();
            (
                ls.clone(),
                ls.clone(),
                ls.clone(),
                kzg,
                ls.clone(),
                ls.clone(),
                ls.clone(),
                ls.clone(),
            )
        } else if args.quick {
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
            // Single-point grid: each system runs only at its largest
            // historical default size. Use `--sizes a,b,c` for an explicit
            // sweep, or `--quick` for the small grid.
            (
                vec![18usize],      // pari        (M=18  → K=2^18 constraints)
                vec![18usize],      // sumcheck    (num_vars=18)
                vec![18usize],      // ipa         (S=18  → N=2^18)
                vec![1usize << 18], // kzg         (n_coeffs=2^18, log_size=18)
                vec![18usize],      // groth16     (log_constraints=18)
                vec![18usize],      // pst13       (n=18)
                vec![18usize],      // hyrax       (n=18, must be even per `n % 2 == 0` assert)
                vec![18usize],      // spartan     (m=18)
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
    eprintln!("source NCLOC (zippel proto vs native_side Rust module):");
    for sys in ALL_SYSTEMS {
        eprintln!(
            "  {:<8} zippel={:>4}  native={:>4}",
            sys,
            zippel_ncloc(sys),
            native_ncloc(sys)
        );
    }
    eprintln!();

    init_csv(&args.out, !args.no_header, args.append).expect("open csv for streaming writes");

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

    eprintln!();
    eprintln!(
        "wrote {} rows to {} in {:.1}s",
        all_rows.len(),
        args.out.display(),
        started.elapsed().as_secs_f64(),
    );
}
