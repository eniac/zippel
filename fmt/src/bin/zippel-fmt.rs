use std::io::{Read, Write};
use std::path::PathBuf;

use fmt::{check, format_source};

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
        let mut src = String::new();
        std::io::stdin().read_to_string(&mut src).unwrap();
        match format_source(&src) {
            Ok(out) => {
                std::io::stdout().write_all(out.as_bytes()).unwrap();
            }
            Err(e) => {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        return;
    }

    let mut has_diff = false;
    for path in &files {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Error reading {}: {}", path.display(), e);
                std::process::exit(1);
            }
        };
        match mode {
            Mode::Check => match check(&src) {
                Ok(()) => {}
                Err(_) => {
                    has_diff = true;
                    eprintln!("{}: not formatted", path.display());
                }
            },
            Mode::Write | Mode::Stdout => match format_source(&src) {
                Ok(out) => {
                    if matches!(mode, Mode::Write) {
                        if out != src {
                            std::fs::write(path, &out).unwrap();
                            eprintln!("{}: formatted", path.display());
                        }
                    } else {
                        std::io::stdout().write_all(out.as_bytes()).unwrap();
                    }
                }
                Err(e) => {
                    eprintln!("Error formatting {}: {}", path.display(), e);
                    std::process::exit(1);
                }
            },
        }
    }

    if matches!(mode, Mode::Check) && has_diff {
        std::process::exit(1);
    }
}
