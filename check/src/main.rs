//! Command-line driver for `zippel-check`.
//!
//! Runs every compile-time check on `.zippel` files (parsing, type checking, Graph IR
//! construction, and the prover/verifier projection) without running the protocol or supplying
//! inputs. Checking needs a concrete value for every `Size` parameter: values come from
//! `--size NAME=VALUE`, and any left unset default to the smallest values (by sum) that keep
//! every dependent range non-empty. Diagnostics go to stderr, one status line per file to stdout.
//!
//! Exit status: 0 if every file checks without errors, 1 if any file has errors or cannot be
//! read, 2 on invalid command-line usage.

use std::collections::HashSet;
use std::process::ExitCode;

use backend::ArkBls12_381;
use clap::Parser;
use graph::UDags;
use lang::ast::module::MAX_DEFAULT_SIZE;
use lang::ast::{CModule, UModule};
use lang::diagnostic::{Diagnostic, Phase, Severity, render_diagnostic};
use lang::id::Tid;
use lang::typ::Kind;
use share::Ctx;
use share::thread;

/// Graph construction and projection are curve-independent; this backend just has to support
/// every operation, including pairings.
type Backend = ArkBls12_381;

/// Runs every compile-time check on `.zippel` files without running the protocol or supplying
/// inputs.
#[derive(Parser)]
#[command(name = "zippel-check")]
struct Cli {
    /// Set a size parameter for every FILE (repeatable). Unset `Size` parameters default to the
    /// smallest values (by sum) that keep every dependent range non-empty.
    #[arg(short = 's', long = "size", value_name = "NAME=VALUE", value_parser = parse_size)]
    sizes: Vec<(Tid, usize)>,

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
        match check_file(path, &given) {
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
fn check_file(path: &str, given: &Ctx<Tid, usize>) -> Option<Report> {
    let src = match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return None;
        }
    };
    let report = thread::run("zippel-check", || check(&src, given));
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

/// Everything `ZippelHandler::compile` does short of running the protocol: parse, concretize
/// sizes, type-check, then build the Graph IR and project each protocol. A stage runs only if
/// the ones before it reported no errors, which would otherwise cascade.
fn check(src: &str, given: &Ctx<Tid, usize>) -> Report {
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

    let params = module.size_params();
    let given: Ctx<Tid, usize> = given
        .iter()
        .filter(|(k, _)| params.contains(k))
        .map(|(k, v)| (k.clone(), *v))
        .collect();
    let Some(sizes) = module.minimal_sizes(&given) else {
        report.diagnostics.push(no_default_sizes(&module, &given));
        return report;
    };

    match module.concretize(&sizes) {
        Err(e) => report.diagnostics.push(e.into()),
        Ok(cmodule) => {
            report.diagnostics.extend(cmodule.typecheck());
            if report.errors() == 0 {
                report.diagnostics.extend(lower(&cmodule));
            }
        }
    }
    report
        .diagnostics
        .sort_by_key(|d| (d.span.start, d.severity));
    report.sizes = Some(sizes);
    report
}

/// Reported when no default values make every range non-empty; anchored at the first `Size`
/// parameter the command line left unset.
fn no_default_sizes(module: &UModule, given: &Ctx<Tid, usize>) -> Diagnostic {
    let unset: Vec<_> = module
        .iter()
        .flat_map(|(sig, _)| sig.typevars.0.iter())
        .filter(|tv| matches!(tv.kind, Kind::SizeVar) && !given.contains(&tv.id.node))
        .map(|tv| &tv.id)
        .collect();
    let names: Vec<String> = unset.iter().map(|id| format!("`{}`", id.node)).collect();
    Diagnostic::error(
        Phase::Type,
        unset.first().map_or(0..0, |id| id.span.clone()),
        "No default sizes make every range non-empty",
    )
    .primary_label(&format!(
        "tried every value up to {MAX_DEFAULT_SIZE} for {}",
        names.join(", ")
    ))
    .note("set the sizes with `--size NAME=VALUE`")
}

/// Build the Graph IR and project the prover and verifier of every protocol, as
/// `ZippelHandler::compile` does for one.
fn lower(module: &CModule) -> Vec<Diagnostic> {
    let dags = match UDags::<Backend>::from_module(module.clone()) {
        Ok(dags) => dags,
        Err(e) => return vec![e.into()],
    };
    let mut diags = Vec::new();
    let mut seen = HashSet::new();
    for proto in dags.protocols() {
        // Like `ZippelHandler::compile`, also project the prover: it can only fail by
        // panicking on a broken internal invariant, reported as an internal compiler error.
        let _ = proto.get_prover();
        if let Err(e) = proto.get_verifier() {
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
