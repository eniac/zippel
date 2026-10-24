//! Command-line driver for `zippel-check`.
//!
//! Runs every compile-time check on `.zippel` files (parsing, type checking, Graph IR
//! construction, and the prover/verifier projection) without running the protocol or supplying
//! inputs. Checking needs a concrete value for every `Size` parameter: values come from
//! `--size NAME=VALUE`, and any left unset default to the smallest values (by sum) that satisfy
//! size constraints and cover function overloads. Diagnostics go to stderr, one status line
//! per file to stdout.
//!
//! Exit status: 0 if every file checks without errors, 1 if any file has errors or cannot be
//! read, 2 on invalid command-line usage.

use std::collections::HashSet;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};
use graph::{Relations, UDags};
use lang::ast::{MAX_DEFAULT_SIZE, SizeSearchError, TypedModule, UModule, minimal_sizes};
use lang::diagnostic::{Diagnostic, Phase, Severity, render_diagnostic};
use lang::id::Tid;
use lang::typ::Kind;
use share::Ctx;

/// The backend to check against: graph construction and projection are curve-independent,
/// but a backend may lack a pairing or large FFT domains, which checking reports.
#[derive(Clone, Copy, Default, ValueEnum)]
enum Backend {
    /// BLS12-381, which supports every operation.
    #[default]
    Bls12_381,
    Bn254,
    Mnt4_298,
    Curve25519,
    Ed25519,
    Secp256k1,
    Pallas,
    Vesta,
}

/// Runs every compile-time check on `.zippel` files without running the protocol or supplying
/// inputs.
#[derive(Parser)]
#[command(name = "zippel-check")]
struct Cli {
    /// Set a size parameter for every FILE (repeatable). Unset `Size` parameters default to the
    /// smallest values (by sum) that satisfy size constraints and cover function overloads.
    #[arg(short = 's', long = "size", value_name = "NAME=VALUE", value_parser = parse_size)]
    sizes: Vec<(Tid, usize)>,

    /// The backend to check against.
    #[arg(short = 'b', long, value_enum, default_value_t)]
    backend: Backend,

    /// Files to check.
    #[arg(required = true, value_name = "FILE")]
    files: Vec<String>,
}

fn parse_size(arg: &str) -> Result<(Tid, usize), String> {
    let (name, value) = arg
        .split_once('=')
        .ok_or_else(|| format!("expected NAME=VALUE for --size, got `{arg}`"))?;
    if name.is_empty() {
        return Err(format!("missing size name in `{arg}`"));
    }
    let value = value
        .parse::<usize>()
        .map_err(|_| format!("size `{name}` must be a non-negative integer, got `{value}`"))?;
    Ok((Tid::new(name), value))
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let given: Ctx<Tid, usize> = Ctx::from(cli.sizes);

    // `--size` names that no checked file used. A file that stopped before choosing sizes
    // cannot vouch that a name is unused.
    let mut unused: Vec<Tid> = given.iter().map(|(name, _)| name.clone()).collect();
    let mut failed = false;
    for path in &cli.files {
        match check_file(path, &given, cli.backend) {
            Some(report) => {
                failed |= report.errors() > 0;
                match &report.sizes {
                    Some(sizes) => unused.retain(|name| !sizes.contains(name)),
                    None => unused.clear(),
                }
            }
            None => {
                failed = true;
                unused.clear();
            }
        }
    }
    for name in unused {
        eprintln!("warning: --size {name}: no checked file has a size parameter named `{name}`");
    }

    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Check one file, printing its diagnostics and status line. Returns the report, or `None` if the
/// file could not be read or the checker panicked.
fn check_file(path: &str, given: &Ctx<Tid, usize>, backend: Backend) -> Option<Report> {
    let src = match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return None;
        }
    };
    // A panic is a compiler bug: report it for this file and go on to the next.
    let report = std::panic::catch_unwind(|| check(&src, given, backend));
    let Ok(report) = report else {
        eprintln!("error: internal compiler error while checking {path}");
        return None;
    };

    for diag in &report.diagnostics {
        eprint!("{}", render_diagnostic(diag, path, &src));
    }

    let errors = report.errors();
    let sizes = report.sizes.clone().unwrap_or_default();
    let described = describe_sizes(&sizes, given);
    if errors == 0 {
        println!("{path}: ok{described}");
    } else {
        let plural = if errors == 1 { "" } else { "s" };
        println!("{path}: {errors} error{plural}{described}");
        let defaulted: Vec<String> = sizes
            .iter()
            .filter(|(name, _)| !given.contains(name))
            .map(|(name, _)| name.to_string())
            .collect();
        if !defaulted.is_empty() {
            eprintln!(
                "note: {} took default values; errors may depend on sizes, so try --size {}=<value>",
                defaulted.join(", "),
                defaulted[0]
            );
        }
    }
    Some(report)
}

/// Outcome of checking one file.
struct Report {
    /// Diagnostics from every stage that ran, ordered by source position.
    diagnostics: Vec<Diagnostic>,
    /// The sizes the module was checked under: the `--size` values naming one of its size
    /// parameters, plus a default for each one left unset. `None` if checking stopped before
    /// sizes were chosen.
    sizes: Option<Ctx<Tid, usize>>,
}

impl Report {
    fn errors(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count()
    }
}

/// Everything `ParsedModule::compile` does short of running the protocol: parse, concretize
/// sizes, type-check, then build the Graph IR and project each protocol. A stage runs only if
/// the ones before it reported no errors, which would otherwise cascade.
fn check(src: &str, given: &Ctx<Tid, usize>, backend: Backend) -> Report {
    let (module, diagnostics) = UModule::parse(src);
    let mut report = Report {
        diagnostics,
        sizes: None,
    };
    let Some(module) = module else {
        return report;
    };
    if report.errors() > 0 {
        return report;
    }

    // Sizes for undeclared names are dropped; one for a range-kinded variable is kept so
    // that `concretize` reports it.
    let params = module.size_params();
    let ranges = module.range_params();
    let given: Ctx<Tid, usize> = given
        .iter()
        .filter(|(k, _)| params.contains(k) || ranges.contains(k))
        .map(|(k, v)| (k.clone(), *v))
        .collect();
    let sizes = if params.iter().all(|name| given.contains(name)) {
        // Explicit sizes and unsized programs retain the compiler's precise diagnostics.
        Ok(given.clone())
    } else {
        minimal_sizes(&module, &given)
    };
    let sizes = match sizes {
        Ok(sizes) => sizes,
        Err(error) => {
            report
                .diagnostics
                .push(no_default_sizes(&module, &given, &error));
            let rejection = match error {
                SizeSearchError::Exhausted { rejection, .. } => Some(rejection),
                SizeSearchError::WorkLimit { rejection, .. } => rejection,
            };
            if let Some(rejection) = rejection {
                let candidate = rejection
                    .candidate
                    .iter()
                    .map(|(name, value)| format!("{name}={value}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                report
                    .diagnostics
                    .extend(rejection.diagnostics.into_iter().map(|diagnostic| {
                        diagnostic.note(&format!("this error occurred with sizes {candidate}"))
                    }));
            }
            return report;
        }
    };

    match module.concretize(&sizes) {
        Err(e) => report.diagnostics.push(e.into()),
        Ok(cmodule) => match cmodule.typecheck() {
            Err(diagnostics) => report.diagnostics.extend(diagnostics),
            Ok(typed) if report.errors() == 0 => report.diagnostics.extend(lower(&typed, backend)),
            Ok(_) => {}
        },
    }
    report
        .diagnostics
        .sort_by_key(|d| (d.span.start, d.severity));
    report.sizes = Some(sizes);
    report
}

/// Reports bounded-search exhaustion at the first unset `Size` parameter.
fn no_default_sizes(
    module: &UModule,
    given: &Ctx<Tid, usize>,
    error: &SizeSearchError,
) -> Diagnostic {
    let unset: Vec<_> = module
        .iter()
        .flat_map(|(sig, _)| sig.typevars.0.iter())
        .filter(|tv| matches!(tv.kind, Kind::SizeVar) && !given.contains(&tv.id.node))
        .map(|tv| &tv.id)
        .collect();
    let names: Vec<String> = unset.iter().map(|id| format!("`{}`", id.node)).collect();
    let diagnostic = Diagnostic::error(
        Phase::Type,
        unset.first().map_or(0..0, |id| id.span.clone()),
        &error.to_string(),
    )
    .primary_label(&format!(
        "unset sizes are bounded by 1..={MAX_DEFAULT_SIZE}: {}",
        names.join(", ")
    ));
    let diagnostic = match error {
        SizeSearchError::Exhausted { .. } => {
            diagnostic.note("this does not rule out valid configurations beyond the search bound")
        }
        SizeSearchError::WorkLimit { .. } => diagnostic
            .note("the search stopped early; untested configurations within the bound may succeed"),
    };
    diagnostic.note("set the sizes with `--size NAME=VALUE` to check a specific configuration")
}

/// [`lower_for`] on the chosen backend.
fn lower(module: &TypedModule, backend: Backend) -> Vec<Diagnostic> {
    match backend {
        Backend::Bls12_381 => lower_for::<backend::ArkBls12_381>(module),
        Backend::Bn254 => lower_for::<backend::ArkBn254>(module),
        Backend::Mnt4_298 => lower_for::<backend::ArkMNT4_298>(module),
        Backend::Curve25519 => lower_for::<backend::ArkCurve25519>(module),
        Backend::Ed25519 => lower_for::<backend::ArkEd25519>(module),
        Backend::Secp256k1 => lower_for::<backend::ArkSecp256k1>(module),
        Backend::Pallas => lower_for::<backend::ArkPallas>(module),
        Backend::Vesta => lower_for::<backend::ArkVesta>(module),
    }
}

/// Build the Graph IR, check that backend `C` can run every protocol, and project the prover
/// and verifier of each, as compilation followed by explicit projection does for one.
fn lower_for<C: backend::Backend>(module: &TypedModule) -> Vec<Diagnostic> {
    let dags = match UDags::<C>::lower(module, Relations::Lower) {
        Ok(dags) => dags,
        Err(e) => return vec![e.into()],
    };
    let mut diags = Vec::new();
    let mut seen = HashSet::new();
    for proto in dags.protocols() {
        if let Err(e) = proto.check_backend() {
            diags.push(Diagnostic::from(e));
            continue;
        }
        // Also project the prover: it can only fail by
        // panicking on a broken internal invariant, reported as an internal compiler error.
        let _ = proto.project_prover();
        if let Err(e) = proto.project_verifier() {
            let d = Diagnostic::from(e);
            if seen.insert((d.span.clone(), d.summary.clone())) {
                diags.push(d);
            }
        }
    }
    diags
}

/// ` [N=2, M=1 (default)]` for the sizes a file was checked under; values not among `given`
/// were defaulted.
fn describe_sizes(sizes: &Ctx<Tid, usize>, given: &Ctx<Tid, usize>) -> String {
    let sizes: Vec<String> = sizes
        .iter()
        .map(|(name, value)| {
            if !given.contains(name) {
                format!("{name}={value} (default)")
            } else {
                format!("{name}={value}")
            }
        })
        .collect();
    if sizes.is_empty() {
        String::new()
    } else {
        format!(" [{}]", sizes.join(", "))
    }
}
