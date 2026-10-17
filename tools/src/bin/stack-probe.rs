//! Stack-use probes for the compiler front end (issue #252).
//!
//! ```text
//! stack-probe min-stack [SHAPE] [N...]   smallest thread stack that compiles each input
//! stack-probe frames BINARY [FILTER...]  largest stack frames of functions in BINARY
//! ```
//!
//! `min-stack` generates a protocol of shape SHAPE (default: every shape) and size N (default:
//! 100 1000 10000), and binary-searches the smallest thread stack on which parsing,
//! concretization, type checking, lowering and projection succeed. Rust aborts the process on a
//! stack overflow, so each attempt runs in a child process. A minimum that grows with N
//! means some pass recurses once per statement or nesting level.
//!
//! `frames` reads each function's prologue (`sub $N,%rsp`, or the `%r11` stack-probe loop LLVM
//! emits for large frames) from `objdump -d`, and lists the largest. FILTER keeps functions
//! whose demangled name contains any of the given strings (default: `lang::`, `graph::`,
//! `fmt::`). Point it at a debug binary, where a big `match` gives every arm its own slots.
//! x86-64 only.

use std::process::{Command, ExitCode};
use std::time::Instant;

use backend::ArkBls12_381;
use graph::{Relations, UDags};
use lang::ast::UModule;
use share::Ctx;

/// Generated inputs: each nests or repeats `r` `n` times inside a Schnorr-shaped protocol.
/// `vectors` nests brackets, so its inferred type is as deep as the input.
const SHAPES: [&str; 7] = [
    "statements",
    "left-sum",
    "right-sum",
    "parens",
    "negation",
    "blocks",
    "vectors",
];

/// Bounds of the search, in KiB.
const MIN_KIB: usize = 64;
const MAX_KIB: usize = 256 * 1024;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("min-stack") => min_stack(&args[1..]),
        Some("frames") if args.len() > 1 => frames(&args[1], &args[2..]),
        Some("child") if args.len() == 4 => child(&args[1], &args[2], &args[3]),
        _ => {
            eprintln!(
                "usage: stack-probe min-stack [SHAPE] [N...]\n       \
                 stack-probe frames BINARY [FILTER...]\nshapes: {}",
                SHAPES.join(", ")
            );
            ExitCode::FAILURE
        }
    }
}

/// The protocol of `shape` and size `n`.
fn source(shape: &str, n: usize) -> Option<String> {
    let exp = match shape {
        "statements" => {
            let lets: String = (1..=n)
                .map(|i| format!("let a{i} = a{} + r; ", i - 1))
                .collect();
            return Some(protocol(&format!("let a0 = r; {lets}let s = a{n};")));
        }
        "left-sum" => vec!["r"; n].join(" + "),
        "right-sum" => format!("{}r{}", "r + (".repeat(n), ")".repeat(n)),
        "parens" => format!("{}r{}", "(".repeat(n), ")".repeat(n)),
        "negation" => format!("{}r", "- ".repeat(n)),
        "blocks" => {
            let open: String = (0..n).rev().map(|i| format!("(let b{i} = ")).collect();
            let close: String = (0..n).map(|i| format!("; b{i})")).collect();
            format!("{open}r{close}")
        }
        "vectors" => {
            let v = format!("{}r{}", "[".repeat(n), "]".repeat(n));
            return Some(protocol(&format!("let _v = {v}; let s = r;")));
        }
        _ => return None,
    };
    Some(protocol(&format!("let s = {exp};")))
}

/// A Schnorr proof whose blinding `s` is computed by `bind`, statements ending in `s`'s binding.
fn protocol(bind: &str) -> String {
    format!(
        "proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) \
         where h == g * x {{\n    let r = random<F>;\n    {bind}\n    u <- g * s;\n    \
         c <- challenge<F>;\n    z <- s + x * c;\n    verify(g * z == u + h * c)\n}}\n"
    )
}

/// Compiles `shape` of size `n` on a thread of `kib` KiB, printing each stage's time.
fn child(shape: &str, n: &str, kib: &str) -> ExitCode {
    let (Some(src), Ok(kib)) = (
        n.parse().ok().and_then(|n| source(shape, n)),
        kib.parse::<usize>(),
    ) else {
        return ExitCode::FAILURE;
    };
    let compiled = std::thread::Builder::new()
        .stack_size(kib * 1024)
        .spawn(move || {
            let mut times = Vec::new();
            let mut clock = Instant::now();
            let mut lap = |stage: &str| {
                times.push(format!("{stage} {:.1?}", clock.elapsed()));
                clock = Instant::now();
            };
            let (module, _) = UModule::parse(&src);
            lap("parse");
            let module = module?.concretize(&Ctx::new()).ok()?;
            lap("concretize");
            let module = module.typecheck().ok()?;
            lap("typecheck");
            let dags = UDags::<ArkBls12_381>::lower(&module, Relations::Lower).ok()?;
            lap("lower");
            for dag in dags.protocols() {
                dag.project_prover();
                dag.project_verifier().ok()?;
            }
            lap("project");
            Some(times.join(", "))
        })
        .expect("spawns")
        .join();
    match compiled {
        Ok(Some(times)) => {
            println!("{times}");
            ExitCode::SUCCESS
        }
        _ => ExitCode::FAILURE,
    }
}

/// Whether `shape` of size `n` compiles on `kib` KiB, and the stage times if so.
fn compiles(shape: &str, n: usize, kib: usize) -> Option<String> {
    let exe = std::env::current_exe().expect("own path");
    let out = Command::new(exe)
        .args(["child", shape, &n.to_string(), &kib.to_string()])
        .output()
        .expect("runs a child");
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_owned())
}

fn min_stack(args: &[String]) -> ExitCode {
    let (shapes, sizes): (Vec<&str>, &[String]) = match args.first() {
        Some(s) if SHAPES.contains(&s.as_str()) => (vec![s.as_str()], &args[1..]),
        _ => (SHAPES.to_vec(), args),
    };
    let sizes: Vec<usize> = if sizes.is_empty() {
        vec![100, 1000, 10_000]
    } else {
        match sizes.iter().map(|s| s.parse()).collect() {
            Ok(sizes) => sizes,
            Err(_) => {
                eprintln!("sizes must be numbers: {sizes:?}");
                return ExitCode::FAILURE;
            }
        }
    };
    println!(
        "{:<11} {:>7} {:>13}  stage times (at the minimum)",
        "shape", "n", "min stack"
    );
    for shape in shapes {
        for &n in &sizes {
            let Some(mut times) = compiles(shape, n, MAX_KIB) else {
                println!(
                    "{shape:<11} {n:>7} {:>13}",
                    format!("> {} MiB", MAX_KIB / 1024)
                );
                continue;
            };
            // Invariant: `hi` compiles, `lo` does not (or is the lower bound).
            let (mut lo, mut hi) = (MIN_KIB, MAX_KIB);
            if let Some(t) = compiles(shape, n, lo) {
                (hi, times) = (lo, t);
            }
            while hi - lo > (hi / 64).max(4) {
                let mid = lo + (hi - lo) / 2;
                match compiles(shape, n, mid) {
                    Some(t) => (hi, times) = (mid, t),
                    None => lo = mid,
                }
            }
            println!("{shape:<11} {n:>7} {:>9} KiB  {times}", hi);
        }
    }
    ExitCode::SUCCESS
}

/// The frame size a function's prologue line allocates, if it is one.
fn frame_size(line: &str) -> Option<usize> {
    let (_, operands) = line.split_once("sub ")?;
    let (imm, reg) = operands.trim().split_once(',')?;
    if !matches!(reg.trim(), "%rsp" | "%r11") {
        return None;
    }
    usize::from_str_radix(imm.trim().strip_prefix("$0x")?, 16).ok()
}

fn frames(binary: &str, filters: &[String]) -> ExitCode {
    let out = match Command::new("objdump")
        .args(["-d", "-C", "--no-show-raw-insn", binary])
        .output()
    {
        Ok(out) if out.status.success() => out,
        Ok(out) => {
            eprintln!("objdump failed: {}", String::from_utf8_lossy(&out.stderr));
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!("cannot run objdump: {e}");
            return ExitCode::FAILURE;
        }
    };
    let default = ["lang::", "graph::", "fmt::"].map(String::from);
    let filters = if filters.is_empty() {
        &default[..]
    } else {
        filters
    };
    let text = String::from_utf8_lossy(&out.stdout);
    // (frame bytes, function), from the first few instructions of each function.
    let mut found: Vec<(usize, &str)> = Vec::new();
    let mut current: Option<(&str, usize)> = None;
    for line in text.lines() {
        if let Some(name) = line.strip_suffix(">:").and_then(|l| l.split_once(" <")) {
            current = Some((name.1, 0));
        } else if let Some((name, seen)) = &mut current {
            *seen += 1;
            if let Some(size) = frame_size(line) {
                found.push((size, name));
                current = None;
            } else if *seen > 16 {
                current = None;
            }
        }
    }
    found.retain(|(_, name)| filters.iter().any(|f| name.contains(f.as_str())));
    found.sort_unstable_by(|a, b| b.cmp(a));
    found.dedup_by(|a, b| a.1 == b.1);
    for (size, name) in found.iter().take(30) {
        println!("{size:>9}  {name}");
    }
    ExitCode::SUCCESS
}
