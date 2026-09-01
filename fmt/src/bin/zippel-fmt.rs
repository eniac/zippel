use std::io::{IsTerminal, Read, Write};
use std::path::PathBuf;

use fmt::{check, format_source, normalize_newlines};
use lang::diagnostic::render_diagnostic;
use similar::{ChangeTag, TextDiff};

fn usage() {
    eprintln!("Usage: zippel-fmt [--check] [--write] [FILE...]");
    eprintln!();
    eprintln!("  --check    Exit 0 if all files are formatted, 1 otherwise.");
    eprintln!("             Prints diff for unformatted files.");
    eprintln!("  --write    Write formatted output back to file.");
    eprintln!("  No flags    Format stdin to stdout.");
    eprintln!("  FILE        Format file(s). Without --write, prints to stdout.");
}

enum Mode {
    Check,
    Write,
    Stdout,
}

/// Render parse diagnostics to stderr.
fn render_diagnostics(diagnostics: &[lang::diagnostic::Diagnostic], filename: &str, src: &str) {
    for diag in diagnostics {
        eprint!("{}", render_diagnostic(diag, filename, src));
    }
}

/// Print a unified diff between `old` and `new` to stderr.
/// Only shows changed lines (no context). Uses ANSI colors when
/// stderr is a terminal.
fn print_diff(old: &str, new: &str, filename: &str) {
    let use_color = std::io::stderr().is_terminal();
    let diff = TextDiff::from_lines(old, new);
    eprintln!("--- {}", filename);
    eprintln!("+++ {}", filename);
    for change in diff.iter_all_changes() {
        // Skip context lines — only show changes.
        if change.tag() == ChangeTag::Equal {
            continue;
        }
        let (prefix, color) = match change.tag() {
            ChangeTag::Delete => ("-", if use_color { "\x1b[31m" } else { "" }),
            ChangeTag::Insert => ("+", if use_color { "\x1b[32m" } else { "" }),
            ChangeTag::Equal => (" ", ""),
        };
        let reset = if use_color { "\x1b[0m" } else { "" };
        eprint!("{}{}{}{}", color, prefix, change.value(), reset);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let mut mode = Mode::Stdout;
    let mut files: Vec<PathBuf> = Vec::new();

    for arg in &args {
        match arg.as_str() {
            "--check" => mode = Mode::Check,
            "--write" => mode = Mode::Write,
            "-h" | "--help" => {
                usage();
                return;
            }
            f if f.starts_with('-') => {
                eprintln!("Unknown flag: {}", f);
                usage();
                std::process::exit(2);
            }
            _ => files.push(PathBuf::from(arg)),
        }
    }

    if files.is_empty() {
        // stdin -> stdout
        let mut raw = String::new();
        std::io::stdin().read_to_string(&mut raw).unwrap();
        let src = normalize_newlines(&raw);
        match format_source(&src) {
            Ok(out) => {
                std::io::stdout().write_all(out.as_bytes()).unwrap();
            }
            Err(diagnostics) => {
                render_diagnostics(&diagnostics, "stdin", &src);
                std::process::exit(1);
            }
        }
        return;
    }

    let mut has_diff = false;
    for path in &files {
        let raw = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Error reading {}: {}", path.display(), e);
                std::process::exit(1);
            }
        };
        // Canonical output is LF. Normalize first so a CRLF working tree
        // (Windows `core.autocrlf=true`) is not reported as unformatted;
        // `--write` restores the file's original line-ending style.
        let crlf = raw.contains("\r\n");
        let src = normalize_newlines(&raw);
        let filename = path.display().to_string();
        match mode {
            Mode::Check => match check(&src) {
                Ok(true) => {}
                Ok(false) => {
                    if has_diff {
                        eprintln!();
                    }
                    has_diff = true;
                    eprintln!("{}: not formatted", filename);
                    if let Ok(formatted) = format_source(&src) {
                        print_diff(&src, &formatted, &filename);
                    }
                }
                Err(diagnostics) => {
                    render_diagnostics(&diagnostics, &filename, &src);
                    std::process::exit(1);
                }
            },
            Mode::Write | Mode::Stdout => match format_source(&src) {
                Ok(out) => {
                    if matches!(mode, Mode::Write) {
                        let styled = if crlf { out.replace('\n', "\r\n") } else { out };
                        if styled != raw {
                            std::fs::write(path, &styled).unwrap();
                            eprintln!("{}: formatted", filename);
                        }
                    } else {
                        std::io::stdout().write_all(out.as_bytes()).unwrap();
                    }
                }
                Err(diagnostics) => {
                    render_diagnostics(&diagnostics, &filename, &src);
                    std::process::exit(1);
                }
            },
        }
    }

    if matches!(mode, Mode::Check) && has_diff {
        std::process::exit(1);
    }
}
