//! Runs every registered non-quarantined benchmark (schnorr, sumcheck, ipa,
//! kzg, pari, groth16, pst13, hyrax) at the rayon thread count of the current
//! process and writes a single CSV.
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
//!   pst13    : N           (multilinear KZG variables)
//!   hyrax    : N           (Hyrax vector dimension parameter)
//!
//! The Zippel-Spartan path is quarantined until its embedded Zippel source no
//! longer uses removed `marginalize(cfg)` syntax; use `spartan_bench` for the
//! native-only Spartan sweep.
//!
//! Thread sweeping is done by running this binary multiple times with
//! different `RAYON_NUM_THREADS`. The wrapper script `run_all.sh` does that
//! and concatenates the CSVs. We tried `rayon::ThreadPool::install` to vary
//! threads in-process, but arkworks' `parallel` feature hangs on a
//! single-thread pool installed mid-process — running with the global pool
//! sized by `RAYON_NUM_THREADS` is the reliable path.

use benchmarks::{Timing, groth16, hyrax, ipa, kzg, pari, pst13, schnorr, sumcheck};
use clap::Parser;
use std::fs::OpenOptions;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

const ALL_SYSTEMS: &[&str] = &[
    "schnorr", "sumcheck", "ipa", "kzg", "pari", "groth16", "pst13", "hyrax",
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

const ZIPPEL_SCHNORR: &str = include_str!("../../../examples/schnorr/schnorr.zippel");
const ZIPPEL_SUMCHECK: &str = include_str!("../../../examples/sumcheck/sumcheck.zippel");
const ZIPPEL_IPA: &str = include_str!("../../../examples/ipa/ipa.zippel");
const ZIPPEL_KZG: &str = include_str!("../../../examples/kzg/kzg.zippel");
const ZIPPEL_PARI: &str = include_str!("../../../examples/pari/pari.zippel");
const ZIPPEL_GROTH16: &str = include_str!("../../../examples/groth16/groth16.zippel");
const ZIPPEL_PST13: &str = include_str!("../../../examples/pst13/pst13.zippel");
const ZIPPEL_HYRAX: &str = include_str!("../../../examples/hyrax/hyrax.zippel");

const NATIVE_IPA_RS: &str = include_str!("../../src/ipa.rs");
const NATIVE_PARI_RS: &str = include_str!("../../src/pari_native.rs");
const NATIVE_HYRAX_RS: &str = include_str!("../../src/hyrax.rs");

// For systems delegating to external crates, native = prover + verifier code
// in the underlying crate (counted once locally with `cloc`-style NCLOC, pinned
// to the version in benchmarks/Cargo.lock at the time these were measured).
// Update when bumping crate versions.
const SCHNORR_EXT_NCLOC: usize = 186; // ark-crypto-primitives-0.5.0 src/signature/schnorr/mod.rs
const SUMCHECK_EXT_NCLOC: usize = 703; // hyperplonk subroutines src/poly_iop/sum_check/{mod,prover,verifier}.rs
const KZG_EXT_NCLOC: usize = 527; // ark-poly-commit-0.5.0 src/kzg10/mod.rs
const GROTH16_EXT_NCLOC: usize = 440; // ark-groth16-0.5.0 src/{prover,verifier,r1cs_to_qap}.rs
const PST13_EXT_NCLOC: usize = 494; // hyperplonk subroutines src/pcs/multilinear_kzg/{mod,srs,util}.rs

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
        _ => 0,
    }
}

fn native_ncloc(sys: &str) -> usize {
    match sys {
        "schnorr" => SCHNORR_EXT_NCLOC,
        "sumcheck" => SUMCHECK_EXT_NCLOC,
        "kzg" => KZG_EXT_NCLOC,
        "groth16" => GROTH16_EXT_NCLOC,
        "pst13" => PST13_EXT_NCLOC,
        "ipa" => count_ncloc_rust(extract_braced_block(NATIVE_IPA_RS, "pub mod native_side")),
        "hyrax" => count_ncloc_rust(extract_braced_block(NATIVE_HYRAX_RS, "pub mod native_side")),
        "pari" => count_ncloc_rust(NATIVE_PARI_RS),
        _ => 0,
    }
}

static CSV_WRITER: OnceLock<Mutex<BufWriter<std::fs::File>>> = OnceLock::new();

fn init_csv(path: &PathBuf, header: bool) -> std::io::Result<()> {
    if header {
        std::fs::write(path, "")?;
    }
    let f = OpenOptions::new().create(true).append(true).open(path)?;
    let mut w = BufWriter::new(f);
    if header {
        writeln!(
            w,
            "system,threads,log_size,prover_time_ms,verifier_time_ms,native_prover_time_ms,native_verifier_time_ms,zippel_ncloc,native_ncloc"
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
    writeln!(
        w,
        "{},{},{},{:.3},{:.3},{:.3},{:.3},{},{}",
        r.system,
        r.threads,
        r.log_size,
        ms(r.zippel.prove),
        ms(r.zippel.verify),
        ms(r.native.prove),
        ms(r.native.verify),
        zippel_ncloc(r.system),
        native_ncloc(r.system),
    )
    .expect("write csv row");
    w.flush().expect("flush csv row");
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
    write_row(r);
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

// Zippel-Spartan is intentionally absent from bench_all until the embedded
// Zippel template in benchmarks/src/spartan.rs is migrated off `marginalize(cfg)`.
// Use the native-only `spartan_bench` binary for Microsoft Spartan sweeps.

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
    let (pari_ms, sumcheck_nvs, ipa_ss, kzg_ns, groth16_log_ns, pst13_ns, hyrax_ns) = if args.quick
    {
        (
            vec![4usize, 8],
            vec![4usize, 8],
            vec![4usize, 6],
            vec![16usize, 256],
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

    init_csv(&args.out, !args.no_header).expect("open csv for streaming writes");

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
