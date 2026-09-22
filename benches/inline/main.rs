//! Single-protocol completeness benchmark with and without pl-table inlining.
//!
//! Usage:
//!   inline [--no-inline] [--backend singular|default]
//!          [--memory-limit-mb MB] <`protocol_name`>
//!
//! Prints JSON to stdout with timing and basis size. Status is one of `ok`,
//! `incomplete`, `crashed` (a real bug/panic), or `oom`.
//!
//! `--memory-limit-mb` caps virtual address space (`RLIMIT_AS`, unix only)
//! around `build_inputs` (ideal construction) and the GB backend call —
//! not the whole process. See `LIMIT_ACTIVE` for the exact boundary and
//! why it's there, and `docs/DECISIONS.md` for a traced example of
//! `build_inputs` alone blowing up memory (a `where`-clause grand product).
//!
//! For batch runs across all protocols with timeout handling, use
//! `inline_all` instead.

#![feature(alloc_error_hook)]

use std::io::Write as _;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use analyses::{CompletenessAnalysis, GbBackendKind, QualifierPropagation};
use backend::ArkBls12_381;
use lang::ast::UModule;
use lang::diagnostic::Severity;
use lang::id::Tid;
use serde::Serialize;
use share::Ctx;
use share::unwrap;

use graph::UDags;

/// True from right before `build_inputs` (ideal construction) to right
/// after the GB backend call returns — the memory-constrained window.
/// Parsing/concretizing/DAG construction before it, and the final
/// verifier-polynomial `run()` after it, are unbounded: a failure there is
/// unambiguously a real bug. Read by `main`'s panic catch to decide
/// `"crashed"` (panic outside this window) vs `"oom"` (inside it).
static LIMIT_ACTIVE: AtomicBool = AtomicBool::new(false);

/// The final JSON line to print on a hard allocator abort, pre-built (while
/// allocation still works) before the memory limit goes into effect. The
/// allocation-error hook below must not allocate, so this is the only way
/// it can report anything.
static OOM_LINE: OnceLock<Vec<u8>> = OnceLock::new();

/// Allocation-error hook: writes the pre-built [`OOM_LINE`] (if any) with no
/// further allocation, then aborts — same as the default hook, but leaves a
/// real status line on stdout for `inline_all` to pick up instead of a
/// silent death.
fn oom_alloc_error_hook(_layout: std::alloc::Layout) {
    if let Some(line) = OOM_LINE.get() {
        let mut out = std::io::stdout();
        let _ = out.write_all(line);
        let _ = out.write_all(b"\n");
        let _ = out.flush();
    }
    std::process::abort();
}

/// Cap the process's virtual address space at `limit_mb` megabytes
/// (`RLIMIT_AS`), inherited by child processes (e.g. Singular). Only
/// lowers the *soft* limit, leaving the hard limit untouched, so it can be
/// raised back via [`restore_memory_limit`] — lowering both would be a
/// one-way ratchet. Returns the previous soft limit on success, `None` if
/// the limit wasn't applied.
#[cfg(unix)]
fn apply_memory_limit(limit_mb: u64) -> Option<u64> {
    let bytes = limit_mb.saturating_mul(1024 * 1024) as libc::rlim_t;

    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut current) } != 0 {
        eprintln!(
            "warning: failed to read current memory limit: {}",
            std::io::Error::last_os_error()
        );
        return None;
    }

    let limit = libc::rlimit {
        rlim_cur: bytes.min(current.rlim_max),
        rlim_max: current.rlim_max,
    };
    if unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const limit) } == 0 {
        Some(current.rlim_cur)
    } else {
        eprintln!(
            "warning: failed to set {limit_mb} MB memory limit: {}",
            std::io::Error::last_os_error()
        );
        None
    }
}

#[cfg(not(unix))]
fn apply_memory_limit(limit_mb: u64) -> Option<u64> {
    eprintln!("warning: --memory-limit-mb is only supported on unix; ignoring {limit_mb} MB limit");
    None
}

/// Restore a soft `RLIMIT_AS` previously returned by [`apply_memory_limit`].
/// Best-effort: if it fails, the process just stays under the tighter
/// limit for the rest of its (already nearly-finished) run.
#[cfg(unix)]
fn restore_memory_limit(previous_soft: u64) {
    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut current) } != 0 {
        return;
    }
    let limit = libc::rlimit {
        rlim_cur: previous_soft as libc::rlim_t,
        rlim_max: current.rlim_max,
    };
    let _ = unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const limit) };
}

#[cfg(not(unix))]
fn restore_memory_limit(_previous_soft: u64) {}

/// JSON output emitted by the `inline` bench. Partial lines (status
/// `"running"`) omit fields that aren't available yet. The final line
/// has the definitive status and all metrics.
#[derive(Serialize, Default)]
struct BenchOutput {
    protocol: String,
    inline: i32,
    status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    build_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gb_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    run_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    basis_size: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_degree: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    num_vars: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    graph_size: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_size: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_max_degree: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_num_vars: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

fn emit(output: &BenchOutput) {
    println!("{}", serde_json::to_string(output).unwrap());
    let _ = std::io::stdout().flush();
}

struct ProtocolConfig {
    name: &'static str,
    path: &'static str,
    sizes: &'static [(&'static str, usize)],
}

static PROTOCOLS: &[ProtocolConfig] = &[
    ProtocolConfig {
        name: "sumcheck",
        path: "examples/sumcheck/sumcheck_full.zippel",
        sizes: &[("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)],
    },
    ProtocolConfig {
        name: "schnorr",
        path: "examples/schnorr/schnorr.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "schnorr_3round",
        path: "examples/schnorr_3round/schnorr_3round.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "okamoto",
        path: "examples/okamoto/okamoto.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "cp",
        path: "examples/cp/cp.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "cds",
        path: "examples/cds/cds.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "hadamard",
        path: "examples/hadamard/hadamard.zippel",
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "coin_proof",
        path: "examples/coin_proof/coin_proof.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "kzg",
        path: "examples/kzg/kzg.zippel",
        sizes: &[("N", 2)],
    },
    ProtocolConfig {
        name: "mle_sumcheck",
        path: "examples/mle_sumcheck/mle_sumcheck.zippel",
        sizes: &[("NUM_VARS", 3), ("MAX_DEGREE_CONST", 1)],
    },
    ProtocolConfig {
        name: "pst13",
        path: "examples/pst13/pst13.zippel",
        sizes: &[("N", 2)],
    },
    ProtocolConfig {
        name: "bccgp",
        path: "examples/bccgp/bccgp.zippel",
        sizes: &[("S", 1)],
    },
    ProtocolConfig {
        name: "groth16",
        path: "examples/groth16/groth16.zippel",
        sizes: &[("M", 1), ("L", 1), ("H", 1)],
    },
    ProtocolConfig {
        name: "ipa",
        path: "examples/ipa/ipa.zippel",
        sizes: &[("S", 1)],
    },
    ProtocolConfig {
        name: "hyrax_podp",
        path: "examples/hyrax_podp/hyrax_podp.zippel",
        sizes: &[("S", 1)],
    },
    ProtocolConfig {
        name: "hyrax_pop",
        path: "examples/hyrax_pop/hyrax_pop.zippel",
        sizes: &[],
    },
    ProtocolConfig {
        name: "hyrax",
        path: "examples/hyrax/hyrax.zippel",
        sizes: &[("L", 2), ("M", 2)],
    },
    ProtocolConfig {
        name: "membership",
        path: "examples/membership/membership.zippel",
        sizes: &[("N", 2), ("M", 2), ("S", 2)],
    },
    ProtocolConfig {
        name: "spartan",
        path: "examples/spartan/spartan.zippel",
        sizes: &[("M", 3)],
    },
    ProtocolConfig {
        name: "dory",
        path: "examples/dory/dory.zippel",
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "r1cs_sigma",
        path: "examples/r1cs_sigma/r1cs_sigma.zippel",
        sizes: &[("N", 2), ("n", 1), ("m", 1)],
    },
    ProtocolConfig {
        name: "hyperplonk_multiset",
        path: "examples/hyperplonk_multiset/hyperplonk_multiset.zippel",
        sizes: &[("S", 3)],
    },
    ProtocolConfig {
        name: "hyperplonk_permutation",
        path: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel",
        sizes: &[("S", 3)],
    },
    ProtocolConfig {
        name: "hyperplonk_zerocheck",
        path: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel",
        sizes: &[("S", 3)],
    },
    ProtocolConfig {
        name: "hyperplonk_productcheck",
        path: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel",
        sizes: &[("S", 3)],
    },
    ProtocolConfig {
        name: "hyperplonk",
        path: "examples/hyperplonk/hyperplonk.zippel",
        sizes: &[("S", 3)],
    },
    ProtocolConfig {
        name: "zk_kzg",
        path: "examples/zk_kzg/zk_kzg.zippel",
        sizes: &[("N", 2)],
    },
    ProtocolConfig {
        name: "kzh",
        path: "examples/kzh/kzh.zippel",
        sizes: &[("NX", 1), ("NY", 1)],
    },
    ProtocolConfig {
        name: "dekart",
        path: "examples/dekart/dekart.zippel",
        sizes: &[("n", 3), ("b", 2), ("l_chunk", 1)],
    },
    ProtocolConfig {
        name: "pari",
        path: "examples/pari/pari.zippel",
        sizes: &[("M", 2), ("N", 1), ("KMN", 3)],
    },
];

fn find_protocol(name: &str) -> Option<&'static ProtocolConfig> {
    PROTOCOLS.iter().find(|p| p.name == name)
}

fn build_sizes_ctx(sizes: &[(&str, usize)]) -> Ctx<Tid, usize> {
    let mut ctx = Ctx::new();
    for &(name, value) in sizes {
        ctx.insert(&Tid::new(name), &value);
    }
    ctx
}

fn run_bench(
    protocol: &ProtocolConfig,
    no_inline: bool,
    backend: GbBackendKind,
    memory_limit_mb: Option<u64>,
) -> String {
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = manifest.join(protocol.path);

    let source = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => return json_error(protocol.name, no_inline, &format!("read failed: {e}")),
    };

    let (module, diags) = UModule::parse(&source);
    let has_errors = diags.iter().any(|d| d.severity == Severity::Error);
    if has_errors {
        return json_error(protocol.name, no_inline, "parse errors");
    }
    let Some(module) = module else {
        return json_error(protocol.name, no_inline, "no module");
    };

    let ctx = build_sizes_ctx(protocol.sizes);
    let concrete = match module.concretize(&ctx) {
        Ok(c) => c,
        Err(e) => return json_error(protocol.name, no_inline, &format!("concretize failed: {e}")),
    };

    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(concrete));
    let proto = gs
        .protocols()
        .into_iter()
        .next()
        .expect("no protocol found");
    let dag = QualifierPropagation::from_dag(proto);

    let inline = !no_inline;
    let graph_size = dag.node_count();

    // Stage 1: Emit graph_size — available before any analysis.
    emit(&BenchOutput {
        protocol: protocol.name.to_string(),
        inline: i32::from(inline),
        status: "running".to_string(),
        graph_size: Some(graph_size),
        ..Default::default()
    });

    // See LIMIT_ACTIVE: the memory-constrained window starts here.
    let mut previous_memory_limit: Option<u64> = None;
    if let Some(limit_mb) = memory_limit_mb {
        let oom_line = serde_json::to_string(&BenchOutput {
            protocol: protocol.name.to_string(),
            inline: i32::from(inline),
            status: "oom".to_string(),
            ..Default::default()
        })
        .unwrap()
        .into_bytes();
        let _ = OOM_LINE.set(oom_line);

        previous_memory_limit = apply_memory_limit(limit_mb);
        if previous_memory_limit.is_some() {
            LIMIT_ACTIVE.store(true, Ordering::SeqCst);
        }
    }

    // Stage 2: Build inputs, compute pre-GB metrics, emit.
    let build_start = Instant::now();
    let inputs = CompletenessAnalysis::<ArkBls12_381>::build_inputs(&dag, inline);
    let build_ms = build_start.elapsed().as_secs_f64() * 1000.0;

    let gen_set_size = inputs.generating_set.len();
    let gen_set_max_degree = inputs
        .generating_set
        .iter()
        .map(analyses::frontend::Polynomial::degree)
        .max()
        .unwrap_or(0);
    let gen_set_num_vars = inputs
        .generating_set
        .iter()
        .flat_map(|p| p.vars().into_iter())
        .collect::<share::Set<analyses::Var>>()
        .len();

    emit(&BenchOutput {
        protocol: protocol.name.to_string(),
        inline: i32::from(inline),
        status: "running".to_string(),
        build_ms: Some(build_ms),
        graph_size: Some(graph_size),
        gen_set_size: Some(gen_set_size),
        gen_set_max_degree: Some(gen_set_max_degree),
        gen_set_num_vars: Some(gen_set_num_vars),
        ..Default::default()
    });

    // Stage 3: Compute GB (expensive — may hang).
    let gb_start = Instant::now();
    let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, backend);
    let gb_ms = gb_start.elapsed().as_secs_f64() * 1000.0;

    // See LIMIT_ACTIVE: the memory-constrained window ends here.
    if let Some(previous) = previous_memory_limit {
        restore_memory_limit(previous);
        LIMIT_ACTIVE.store(false, Ordering::SeqCst);
    }

    let basis_size = ca.basis.polys.len();
    let max_degree = ca
        .basis
        .polys
        .iter()
        .map(analyses::frontend::Polynomial::degree)
        .max()
        .unwrap_or(0);
    let num_vars = ca.basis.vars().len();

    // Emit post-GB metrics before run() — survives if run() hangs or is killed.
    emit(&BenchOutput {
        protocol: protocol.name.to_string(),
        inline: i32::from(inline),
        status: "running".to_string(),
        build_ms: Some(build_ms),
        gb_ms: Some(gb_ms),
        basis_size: Some(basis_size),
        max_degree: Some(max_degree),
        num_vars: Some(num_vars),
        graph_size: Some(graph_size),
        gen_set_size: Some(gen_set_size),
        gen_set_max_degree: Some(gen_set_max_degree),
        gen_set_num_vars: Some(gen_set_num_vars),
        ..Default::default()
    });

    let run_start = Instant::now();
    let result = ca.run();
    let run_ms = run_start.elapsed().as_secs_f64() * 1000.0;

    let (status, error) = match result {
        Ok(()) => ("ok", None),
        Err(e) => ("incomplete", Some(format!("{e}"))),
    };

    serde_json::to_string(&BenchOutput {
        protocol: protocol.name.to_string(),
        inline: i32::from(inline),
        status: status.to_string(),
        build_ms: Some(build_ms),
        gb_ms: Some(gb_ms),
        run_ms: Some(run_ms),
        basis_size: Some(basis_size),
        max_degree: Some(max_degree),
        num_vars: Some(num_vars),
        graph_size: Some(graph_size),
        gen_set_size: Some(gen_set_size),
        gen_set_max_degree: Some(gen_set_max_degree),
        gen_set_num_vars: Some(gen_set_num_vars),
        error,
    })
    .unwrap()
}

fn json_error(name: &str, no_inline: bool, error: &str) -> String {
    serde_json::to_string(&BenchOutput {
        protocol: name.to_string(),
        inline: i32::from(!no_inline),
        status: "crashed".to_string(),
        error: Some(error.to_string()),
        ..Default::default()
    })
    .unwrap()
}

fn main() {
    // cargo bench always injects `--bench` into the args (even with
    // harness = false). Filter it out.
    let args: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| a != "--bench")
        .collect();

    let mut no_inline = false;
    let mut backend = GbBackendKind::default();
    let mut memory_limit_mb: Option<u64> = None;
    let mut protocol_name: Option<&str> = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--no-inline" => no_inline = true,
            "--backend" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--backend requires a value (singular|default)");
                    std::process::exit(2);
                }
                backend = match args[i].as_str() {
                    "singular" | "Singular" => GbBackendKind::Singular,
                    "default" => GbBackendKind::default(),
                    other => {
                        eprintln!("unknown backend: {other}");
                        std::process::exit(2);
                    }
                };
            }
            "--memory-limit-mb" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--memory-limit-mb requires a value (megabytes)");
                    std::process::exit(2);
                }
                memory_limit_mb = Some(args[i].parse().unwrap_or_else(|_| {
                    eprintln!("invalid --memory-limit-mb value: {}", args[i]);
                    std::process::exit(2);
                }));
            }
            other if protocol_name.is_none() => protocol_name = Some(other),
            other => {
                eprintln!("unexpected argument: {other}");
                std::process::exit(2);
            }
        }
        i += 1;
    }

    let Some(protocol_name) = protocol_name else {
        eprintln!(
            "usage: inline [--no-inline] [--backend singular|default] \
             [--memory-limit-mb MB] <protocol_name>"
        );
        eprintln!();
        eprintln!("available protocols:");
        for p in PROTOCOLS {
            eprintln!("  {}", p.name);
        }
        std::process::exit(2);
    };

    let Some(protocol) = find_protocol(protocol_name) else {
        eprintln!("unknown protocol: {protocol_name}");
        std::process::exit(2);
    };

    std::alloc::set_alloc_error_hook(oom_alloc_error_hook);

    // Run in a thread with a large stack to avoid stack overflow.
    let protocol_clone = protocol.name;
    let result = share::thread::run("inline-bench", move || {
        run_bench(protocol, no_inline, backend, memory_limit_mb)
    })
    .unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
            .unwrap_or_else(|| "thread panicked".to_string());
        // See LIMIT_ACTIVE for what this checks.
        let status = if LIMIT_ACTIVE.load(Ordering::SeqCst) {
            "oom"
        } else {
            "crashed"
        };
        serde_json::to_string(&BenchOutput {
            protocol: protocol_clone.to_string(),
            inline: i32::from(!no_inline),
            status: status.to_string(),
            error: Some(message),
            ..Default::default()
        })
        .unwrap()
    });

    println!("{result}");
}
