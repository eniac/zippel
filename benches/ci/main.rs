//! CI-only measurements using registered example inputs and public Zippel APIs.

use std::{collections::BTreeMap, time::Instant};

use analyses::GbBackendKind;
use backend::{ArkConfig, HasOpFactory};
use clap::{Parser, ValueEnum};
use zippel::{Analysis, CompileOptions, ParsedModule};

#[allow(dead_code)]
#[path = "../../examples/common/mod.rs"]
mod common;
mod profile;

#[path = "../../examples/registry.rs"]
mod registry;

macro_rules! examples {
    ($($name:ident),* $(,)?) => {
        const NAMES: &[&str] = &[$(stringify!($name)),*];
        fn dispatch(args: &Args) -> Result<(), String> {
            match args.example.as_str() {
                $(stringify!($name) => benchmark(&registry::$name::spec(), args),)*
                _ => unreachable!("clap validates example names"),
            }
        }
    };
}

registry::with_examples!(examples);

#[derive(Clone, Copy, ValueEnum)]
enum Mode {
    Run,
    Analyze,
}

#[derive(Parser)]
struct Args {
    #[arg(value_enum)]
    mode: Mode,
    #[arg(value_parser = clap::builder::PossibleValuesParser::new(NAMES))]
    example: String,
    #[arg(long = "size", value_parser = parse_size)]
    sizes: Vec<(String, usize)>,
    #[arg(long, default_value_t = 1, value_parser = clap::value_parser!(u8).range(1..=3))]
    samples: u8,
    #[arg(long, value_parser = ["completeness", "zk", "soundness"])]
    analysis: Option<String>,
}

fn parse_size(value: &str) -> Result<(String, usize), String> {
    let (name, value) = value.split_once('=').ok_or("expected NAME=VALUE")?;
    Ok((name.to_owned(), value.parse().map_err(|_| "invalid size")?))
}

fn measure<T>(
    times: &mut BTreeMap<&'static str, Vec<f64>>,
    name: &'static str,
    f: impl FnOnce() -> T,
) -> T {
    let start = Instant::now();
    let result = profile::measure(name, f);
    times
        .entry(name)
        .or_default()
        .push(start.elapsed().as_secs_f64() * 1000.0);
    result
}

fn benchmark<C: ArkConfig + HasOpFactory>(
    spec: &common::ExampleSpec<C>,
    args: &Args,
) -> Result<(), String> {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(spec.source);
    let module = ParsedModule::load(source).map_err(|e| e.to_string())?;
    let given = if args.sizes.is_empty() {
        spec.defaults
            .iter()
            .map(|&(name, value)| (name.to_owned(), value))
            .collect()
    } else {
        args.sizes.clone()
    };
    let sizes = common::resolve(&module, &given)?;
    if let Some(validate) = spec.validate {
        validate(&sizes, matches!(args.mode, Mode::Analyze))?;
    }
    // An unmeasured first compile pays one-time process costs (lazy statics,
    // allocator growth), which would otherwise make sample 1 an outlier.
    module
        .compile::<C>(&sizes, CompileOptions::default())
        .map_err(|e| e.to_string())?;
    let mut times = BTreeMap::new();
    let mut compiled = None;
    for _ in 0..args.samples {
        compiled = Some(measure(&mut times, "compile", || {
            module
                .compile::<C>(&sizes, CompileOptions::default())
                .map_err(|e| e.to_string())
        })?);
    }
    let protocol = compiled.expect("positive sample count");
    let mut config = serde_json::json!({
        "sizes": sizes.iter().map(|(name, value)| (name.to_string(), *value)).collect::<BTreeMap<_, _>>(),
        "source": spec.source,
        "curve": std::any::type_name::<C>().rsplit("::").next().unwrap(),
        "analysis": null,
        "rounds": [],
    });
    match args.mode {
        Mode::Run => {
            let prover = protocol.project_prover();
            let verifier = protocol.project_verifier().map_err(|e| e.to_string())?;
            drop(protocol);
            for _ in 0..args.samples {
                // Fresh inputs per sample, generated outside all measured
                // regions, so the sample spread includes input variation.
                let inputs = (spec.make_inputs)(&sizes);
                let verifier_inputs = inputs.clone();
                let proof = measure(&mut times, "prove", || {
                    prover.prove(inputs).map_err(|e| e.to_string())
                })?;
                let passed = measure(&mut times, "verify", || {
                    verifier
                        .verify(proof, verifier_inputs)
                        .map_err(|e| e.to_string())
                })?;
                if !passed {
                    return Err("verification failed".into());
                }
            }
        }
        Mode::Analyze => {
            let pass = args
                .analysis
                .as_deref()
                .map_or_else(
                    || {
                        spec.analyses
                            .iter()
                            .find(|pass| matches!(pass, Analysis::Completeness))
                            .or_else(|| spec.analyses.first())
                    },
                    |selected| {
                        spec.analyses
                            .iter()
                            .find(|pass| pass.label().eq_ignore_ascii_case(selected))
                    },
                )
                .ok_or("requested analysis is not registered")?;
            config["analysis"] = serde_json::json!(pass.label().to_lowercase());
            if let Analysis::Soundness(rounds) = pass {
                config["rounds"] = serde_json::json!(rounds);
            }
            protocol.prepare_analysis().map_err(|e| e.to_string())?;
            let mut prepared = None;
            for _ in 0..args.samples {
                prepared = Some(measure(&mut times, "prepare", || {
                    protocol.prepare_analysis().map_err(|e| e.to_string())
                })?);
            }
            let prepared = prepared.expect("positive sample count");
            for _ in 0..args.samples {
                measure(&mut times, "analysis", || {
                    prepared
                        .run(*pass, GbBackendKind::Singular)
                        .map_err(|e| e.to_string())
                })?;
            }
        }
    }
    println!(
        "{}",
        serde_json::json!({"status": "ok", "config": config, "ms": times})
    );
    Ok(())
}

fn main() -> std::process::ExitCode {
    let args = Args::parse();
    let result = dispatch(&args);
    match result {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::FAILURE
        }
    }
}
