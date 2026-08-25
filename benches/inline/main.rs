//! Single-protocol completeness benchmark with and without pl-table inlining.
//!
//! Usage:
//!   inline [--no-inline] [--backend singular|default] <`protocol_name`>
//!
//! Prints JSON to stdout with timing and basis size.
//! Exit code 0 = analysis succeeded, 1 = analysis error, 2 = panic/crash.
//!
//! For batch runs across all protocols with timeout/OOM handling, use
//! `inline_all` instead.

use std::time::Instant;

use analyses::{CompletenessAnalysis, GbBackendKind, QualifierPropagation};
use backend::ArkBls12_381;
use lang::ast::UModule;
use lang::diagnostic::Severity;
use lang::id::Tid;
use share::Ctx;
use share::unwrap;

use graph::UDags;

const STACK_SIZE: usize = 256 * 1024 * 1024;

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
        sizes: &[("S", 0)],
    },
    ProtocolConfig {
        name: "groth16",
        path: "examples/groth16/groth16.zippel",
        sizes: &[("M", 1), ("L", 1), ("H", 1)],
    },
    ProtocolConfig {
        name: "ipa",
        path: "examples/ipa/ipa.zippel",
        sizes: &[("S", 0)],
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
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "hyperplonk_permutation",
        path: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel",
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "hyperplonk_zerocheck",
        path: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel",
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "hyperplonk_productcheck",
        path: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel",
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "hyperplonk",
        path: "examples/hyperplonk/hyperplonk.zippel",
        sizes: &[("S", 2)],
    },
    ProtocolConfig {
        name: "zk_kzg",
        path: "examples/zk_kzg/zk_kzg.zippel",
        sizes: &[("N", 2)],
    },
    ProtocolConfig {
        name: "kzh",
        path: "examples/kzh/kzh.zippel",
        sizes: &[("NX", 2), ("NY", 2)],
    },
    ProtocolConfig {
        name: "dekart",
        path: "examples/dekart/dekart.zippel",
        sizes: &[("n", 3), ("b", 2), ("l_chunk", 1), ("h_deg", 3)],
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

fn run_bench(protocol: &ProtocolConfig, no_inline: bool, backend: GbBackendKind) -> String {
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = manifest.join(protocol.path);

    let source = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            return json_error(protocol.name, no_inline, &format!("read failed: {e}"));
        }
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

    let from_input_start = Instant::now();
    let mut ca = CompletenessAnalysis::from_input_with_options(&dag, backend, inline);
    let from_input_ms = from_input_start.elapsed().as_secs_f64() * 1000.0;

    let basis_size = ca.basis.polys.len();
    let max_degree = ca
        .basis
        .polys
        .iter()
        .map(analyses::frontend::Polynomial::degree)
        .max()
        .unwrap_or(0);
    let num_vars = ca.basis.vars().len();
    let graph_size = dag.node_count();

    let run_start = Instant::now();
    let result = ca.run();
    let run_ms = run_start.elapsed().as_secs_f64() * 1000.0;

    let (status, error) = match result {
        Ok(()) => ("ok", String::new()),
        Err(e) => ("incomplete", format!("{e}")),
    };

    format!(
        r#"{{"protocol":"{}","inline":{},"status":"{}","from_input_ms":{:.3},"run_ms":{:.3},"basis_size":{},"max_degree":{},"num_vars":{},"graph_size":{},"error":"{}"}}"#,
        protocol.name,
        i32::from(inline),
        status,
        from_input_ms,
        run_ms,
        basis_size,
        max_degree,
        num_vars,
        graph_size,
        error.replace('"', "'")
    )
}

fn json_error(name: &str, no_inline: bool, error: &str) -> String {
    format!(
        r#"{{"protocol":"{}","inline":{},"status":"error","error":"{}"}}"#,
        name,
        i32::from(!no_inline),
        error.replace('"', "'")
    )
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
            other if protocol_name.is_none() => protocol_name = Some(other),
            other => {
                eprintln!("unexpected argument: {other}");
                std::process::exit(2);
            }
        }
        i += 1;
    }

    let Some(protocol_name) = protocol_name else {
        eprintln!("usage: inline [--no-inline] [--backend singular|default] <protocol_name>");
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

    // Run in a thread with a large stack to avoid stack overflow.
    let protocol_clone = protocol.name;
    let result = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || run_bench(protocol, no_inline, backend))
        .expect("failed to spawn thread")
        .join()
        .unwrap_or_else(|_| {
            format!(
                r#"{{"protocol":"{}","inline":{},"status":"panic","error":"thread panicked"}}"#,
                protocol_clone,
                i32::from(!no_inline)
            )
        });

    println!("{result}");
}
