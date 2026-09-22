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

use std::io::IsTerminal;
use std::process::ExitCode;

use check::check;
use lang::check::CheckReport;
use lang::diagnostic::render_diagnostic_with_color;
use lang::id::Tid;
use share::Ctx;

/// Matches the stack `ZippelHandler::compile` gives its compiler thread; inference recurses once
/// per statement of a body.
const STACK_SIZE: usize = 64 * 1024 * 1024;

fn usage() {
    eprintln!("Usage: zippel-check [--size NAME=VALUE]... [--verbose] FILE...");
    eprintln!();
    eprintln!("  -s, --size NAME=VALUE  Set a size parameter for every FILE (repeatable).");
    eprintln!("                         Unset `Size` parameters default to the smallest");
    eprintln!("                         value that keeps every dependent range non-empty.");
    eprintln!("  -v, --verbose          Also print the full typing judgement of each type error.");
    eprintln!("  -h, --help             Print this help.");
}

struct Options {
    sizes: Ctx<Tid, usize>,
    verbose: bool,
    files: Vec<String>,
}

enum Parsed {
    Run(Options),
    Help,
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

fn parse_args(mut args: impl Iterator<Item = String>) -> Result<Parsed, String> {
    let mut opts = Options {
        sizes: Ctx::new(),
        verbose: false,
        files: Vec::new(),
    };
    while let Some(arg) = args.next() {
        let size_arg = if arg == "-s" || arg == "--size" {
            Some(args.next().ok_or("--size requires NAME=VALUE")?)
        } else {
            arg.strip_prefix("--size=").map(str::to_string)
        };
        if let Some(size_arg) = size_arg {
            let (name, value) = parse_size(&size_arg)?;
            opts.sizes.insert(&name, &value);
            continue;
        }
        match arg.as_str() {
            "-v" | "--verbose" => opts.verbose = true,
            "-h" | "--help" => return Ok(Parsed::Help),
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            _ => opts.files.push(arg),
        }
    }
    if opts.files.is_empty() {
        return Err("no input files".to_string());
    }
    Ok(Parsed::Run(opts))
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
    let report = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("zippel-check".to_string())
            .stack_size(STACK_SIZE)
            .spawn_scoped(scope, || check(&src, &opts.sizes))
            .expect("failed to spawn checker thread")
            .join()
    });
    let Ok(report) = report else {
        eprintln!("error: internal compiler error while checking {path}");
        return None;
    };

    let color = std::io::stderr().is_terminal();
    for finding in &report.findings {
        eprint!(
            "{}",
            render_diagnostic_with_color(&finding.diagnostic, path, &src, color)
        );
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
    let opts = match parse_args(std::env::args().skip(1)) {
        Ok(Parsed::Run(opts)) => opts,
        Ok(Parsed::Help) => {
            usage();
            return ExitCode::SUCCESS;
        }
        Err(msg) => {
            eprintln!("error: {msg}\n");
            usage();
            return ExitCode::from(2);
        }
    };

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
