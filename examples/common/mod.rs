//! Shared compilation, execution and analysis for registered examples.
use backend::{Backend, Value};
use lang::{
    diagnostic::render_diagnostic,
    id::{Tid, Vid},
};
use share::Ctx;
use std::{path::Path, time::Instant};
pub use zippel::Analysis;
use zippel::{
    CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    proof_size_bytes,
};

use analyses::GbBackendKind;

/// A pass selected by the caller; protocol parameters live in [`Analysis`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnalysisKind {
    Completeness,
    Zk,
    Soundness,
}

impl AnalysisKind {
    const fn matches(self, analysis: Analysis<'_>) -> bool {
        matches!(
            (self, analysis),
            (Self::Completeness, Analysis::Completeness)
                | (Self::Zk, Analysis::Zk)
                | (Self::Soundness, Analysis::Soundness(_))
        )
    }
}

/// Work requested for an example.
#[derive(Clone, Copy, Debug)]
pub enum Operation {
    Run,
    Analyze {
        pass: Option<AnalysisKind>,
        backend: GbBackendKind,
    },
}

/// Sizes and work supplied to the harness, independently of CLI parsing.
pub struct Request {
    pub sizes: Vec<(String, usize)>,
    pub operation: Operation,
}

type ValidateSizes = fn(&Ctx<Tid, usize>, bool) -> Result<(), String>;
type MakeInputs<C> = fn(&Ctx<Tid, usize>) -> Ctx<Vid, Value<C>>;

/// Protocol-specific data; orchestration belongs to this module.
pub struct ExampleSpec<C: Backend> {
    pub source: &'static str,
    /// Complete size set used only when no sizes are supplied.
    pub defaults: &'static [(&'static str, usize)],
    pub validate: Option<ValidateSizes>,
    pub make_inputs: MakeInputs<C>,
    pub analyses: &'static [Analysis<'static>],
}

/// Read a registered size from the resolved context.
pub fn size(sizes: &Ctx<Tid, usize>, name: &str) -> usize {
    sizes[&Tid::new(name)]
}

fn usage(message: impl std::fmt::Display) -> u8 {
    eprintln!("error: {message}");
    2
}

/// Resolve sizes once, validating names before compilation or allocation.
pub fn resolve(
    module: &ParsedModule,
    given: &[(String, usize)],
) -> Result<Ctx<Tid, usize>, String> {
    let params = module.size_params();
    let mut sizes = Ctx::new();
    for (name, value) in given {
        let id = Tid::new(name);
        if !params.contains(&id) {
            return Err(format!("unknown size `{name}`"));
        }
        sizes.insert(&id, value);
    }
    let mut missing: Vec<_> = params
        .iter()
        .filter(|id| !sizes.contains(id))
        .map(|id| format!("--size {id}=VALUE"))
        .collect();
    missing.sort();
    if !missing.is_empty() {
        return Err(format!("missing required sizes: {}", missing.join(" ")));
    }
    Ok(sizes)
}

/// Execute one registered example and return its process status.
pub fn run<C: analyses::AnalysisBackend>(
    name: &str,
    spec: &ExampleSpec<C>,
    request: &Request,
) -> u8 {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(spec.source);
    let module = match ParsedModule::load(&path) {
        Ok(module) => module,
        Err(error) => {
            eprintln!("{error}");
            return 1;
        }
    };
    for diagnostic in module.diagnostics() {
        eprint!(
            "{}",
            render_diagnostic(diagnostic, module.source_name(), module.source())
        );
    }
    let given = if request.sizes.is_empty() {
        spec.defaults
            .iter()
            .map(|&(name, value)| (name.to_owned(), value))
            .collect()
    } else {
        request.sizes.clone()
    };
    let sizes = match resolve(&module, &given) {
        Ok(sizes) => sizes,
        Err(e) => return usage(format!("{name}: {e}")),
    };
    if let Operation::Analyze { pass, .. } = request.operation
        && (spec.analyses.is_empty()
            || pass.is_some_and(|kind| !spec.analyses.iter().any(|p| kind.matches(*p))))
    {
        return usage(format!(
            "{name}: requested analysis is not registered (see --help)"
        ));
    }
    if let Some(validate) = spec.validate
        && let Err(e) = validate(
            &sizes,
            matches!(request.operation, Operation::Analyze { .. }),
        )
    {
        return usage(format!("{name}: {e}"));
    }
    let protocol = match module.compile::<C>(&sizes, CompileOptions::default()) {
        Ok(protocol) => protocol,
        Err(error) => {
            eprintln!("{error}");
            return 2;
        }
    };
    for diagnostic in protocol
        .diagnostics()
        .iter()
        .skip(module.diagnostics().len())
    {
        eprint!(
            "{}",
            render_diagnostic(diagnostic, module.source_name(), module.source())
        );
    }
    if let Operation::Analyze {
        backend: GbBackendKind::Singular,
        ..
    } = request.operation
        && let Err(e) = std::process::Command::new("Singular")
            .arg("--version")
            .output()
    {
        eprintln!("Singular backend unavailable: {e}");
        return 1;
    }
    let described = sizes
        .iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join(", ");
    let curve = std::any::type_name::<C>().rsplit("::").next().unwrap();
    print!(
        "{name} | {curve} | sizes={}",
        if described.is_empty() {
            "none"
        } else {
            &described
        }
    );
    if let Operation::Analyze { backend, .. } = request.operation {
        print!(
            " | backend={}",
            match backend {
                GbBackendKind::Singular => "singular",
                GbBackendKind::ArkGb => "ark-gb",
            }
        );
    }
    println!();
    match request.operation {
        Operation::Run => {
            let prover = protocol.project_prover();
            let verifier = match protocol.project_verifier() {
                Ok(verifier) => verifier,
                Err(error) => {
                    eprintln!("{error}");
                    return 2;
                }
            };
            drop(protocol);
            run_protocol(&prover, &verifier, (spec.make_inputs)(&sizes))
        }
        Operation::Analyze { pass, backend } => {
            run_analyses(&protocol, spec.analyses, pass, backend)
        }
    }
}

fn run_analyses<C: analyses::AnalysisBackend>(
    protocol: &CompiledProtocol<C>,
    analyses: &[Analysis<'_>],
    selected: Option<AnalysisKind>,
    backend: GbBackendKind,
) -> u8 {
    let prepared = match protocol.prepare_analysis() {
        Ok(prepared) => prepared,
        Err(error) => {
            eprintln!("{error}");
            return 1;
        }
    };
    let passes = analyses
        .iter()
        .copied()
        .filter(|pass| selected.is_none_or(|kind| kind.matches(*pass)));
    let mut failed = false;
    for pass in passes {
        let start = Instant::now();
        let result = prepared.run(pass, backend);
        let status = match result {
            Ok(()) => "PASS",
            Err(e) => {
                failed = true;
                eprintln!("{}: {e}", pass.label());
                if matches!(e, analyses::AnalysisError::Backend(_)) {
                    "ERROR"
                } else {
                    "FAIL"
                }
            }
        };
        println!(
            "{}: {status} | {:.2} ms",
            pass.label(),
            start.elapsed().as_secs_f64() * 1000.0
        );
    }
    u8::from(failed)
}

fn run_protocol<C: analyses::AnalysisBackend>(
    prover: &CompiledProver<C>,
    verifier: &CompiledVerifier<C>,
    inputs: Ctx<Vid, Value<C>>,
) -> u8 {
    let start = Instant::now();
    let proof = match prover.prove(inputs.clone()) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Prover: {e}");
            return 1;
        }
    };
    println!("Prover: {:.2} ms", start.elapsed().as_secs_f64() * 1000.0);
    println!(
        "Proof: {} bytes, {} elements",
        proof_size_bytes::<C>(&proof),
        proof.len()
    );
    let start = Instant::now();
    let passed = match verifier.verify(proof, inputs) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Verifier: {e}");
            return 1;
        }
    };
    println!("Verifier: {:.2} ms", start.elapsed().as_secs_f64() * 1000.0);
    println!("Verification: {}", if passed { "PASS" } else { "FAIL" });
    u8::from(!passed)
}

/// Check that `2^NAME` is representable as a `usize`.
pub fn check_power_of_two(sizes: &Ctx<Tid, usize>, name: &str) -> Result<(), String> {
    if size(sizes, name) >= usize::BITS as usize {
        return Err(format!("{name}={} overflows 2^{name}", size(sizes, name)));
    }
    Ok(())
}

/// Check that `2^(A+B)` is representable as a `usize`.
pub fn check_power_of_two_sum(sizes: &Ctx<Tid, usize>, a: &str, b: &str) -> Result<(), String> {
    let a_value = size(sizes, a);
    let b_value = size(sizes, b);
    let sum = a_value
        .checked_add(b_value)
        .ok_or_else(|| format!("{a}={a_value}, {b}={b_value}: {a}+{b} exceeds usize::MAX"))?;
    if sum >= usize::BITS as usize {
        return Err(format!(
            "{a}={a_value}, {b}={b_value}: 2^({a}+{b}) = 2^{sum} does not fit in usize; {a}+{b} must be < {}",
            usize::BITS
        ));
    }
    Ok(())
}
