//! Command-line driver for `zippel-check`.
//!
//! Runs every compile-time check on `.zippel` files (parsing, type checking, Graph IR
//! construction, and the prover/verifier projection) without running the protocol or supplying
//! inputs. Checking needs a concrete value for every `Size` parameter: values come from
//! `--size NAME=VALUE`, and any left unset default to the smallest value that keeps every
//! dependent range non-empty. Diagnostics go to stderr, one status line per file to stdout.
//!
//! Exit status: 0 if every file checks without errors, 1 if any file has errors or cannot be
//! read, 2 on invalid command-line usage.

use std::process::ExitCode;

use check::check;
use clap::Parser;
use lang::check::CheckReport;
use lang::diagnostic::render_diagnostic;
use lang::id::Tid;
use share::Ctx;
use share::thread;

/// Runs every compile-time check on `.zippel` files without running the protocol or supplying
/// inputs.
#[derive(Parser)]
#[command(name = "zippel-check")]
struct Cli {
    /// Set a size parameter for every FILE (repeatable). Unset `Size` parameters default to the
    /// smallest value that keeps every dependent range non-empty.
    #[arg(short = 's', long = "size", value_name = "NAME=VALUE", value_parser = parse_size)]
    sizes: Vec<(Tid, usize)>,

    /// Also print the full typing judgement of each type error.
    #[arg(short, long)]
    verbose: bool,

    /// Files to check.
    #[arg(required = true, value_name = "FILE")]
    files: Vec<String>,
}

struct Options {
    sizes: Ctx<Tid, usize>,
    verbose: bool,
    files: Vec<String>,
}

impl From<Cli> for Options {
    fn from(cli: Cli) -> Self {
        Options {
            sizes: Ctx::from(cli.sizes),
            verbose: cli.verbose,
            files: cli.files,
        }
    }
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

fn describe_sizes(report: &CheckReport) -> String {
    let sizes: Vec<String> = report
        .sizes
        .iter()
        .map(|(name, value)| {
            if report.defaulted.contains(name) {
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

/// Check one file, printing its diagnostics and status line. Returns the report, or `None` if the
/// file could not be read or the checker panicked.
fn check_file(path: &str, opts: &Options) -> Option<CheckReport> {
    let src = match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return None;
        }
    };
    let report = thread::run("zippel-check", || check(&src, &opts.sizes));
    let Ok(report) = report else {
        eprintln!("error: internal compiler error while checking {path}");
        return None;
    };

    for finding in &report.findings {
        eprint!("{}", render_diagnostic(&finding.diagnostic, path, &src));
        if opts.verbose
            && let Some(detail) = &finding.detail
        {
            eprintln!("{detail}\n");
        }
    }

    let errors = report
        .findings
        .iter()
        .filter(|f| f.diagnostic.severity == lang::diagnostic::Severity::Error)
        .count();
    let sizes = describe_sizes(&report);
    if errors == 0 {
        println!("{path}: ok{sizes}");
    } else {
        let plural = if errors == 1 { "" } else { "s" };
        println!("{path}: {errors} error{plural}{sizes}");
        if !report.defaulted.is_empty() {
            let names: Vec<String> = report.defaulted.iter().map(ToString::to_string).collect();
            eprintln!(
                "note: {} took default values; errors may depend on sizes, so try --size {}=<value>",
                names.join(", "),
                names[0]
            );
        }
    }
    Some(report)
}

fn main() -> ExitCode {
    let opts = Options::from(Cli::parse());

    let mut failed = false;
    let mut unknown_everywhere: Option<Vec<Tid>> = None;
    for path in &opts.files {
        match check_file(path, &opts) {
            Some(report) => {
                failed |= report.has_errors();
                unknown_everywhere = Some(match unknown_everywhere {
                    None => report.unknown,
                    Some(prev) => prev
                        .into_iter()
                        .filter(|name| report.unknown.contains(name))
                        .collect(),
                });
            }
            None => failed = true,
        }
    }
    for name in unknown_everywhere.unwrap_or_default() {
        eprintln!("warning: --size {name}: no checked file has a size parameter named `{name}`");
    }

    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
