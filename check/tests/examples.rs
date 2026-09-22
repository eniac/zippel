//! Runs the `zippel-check` binary over every bundled example and over a few ill-formed inputs.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Examples that only pass at sizes larger than the defaults `zippel-check` picks. The
/// values match the sizes their `main.rs` harnesses compile with.
const EXAMPLE_SIZES: &[(&str, &[&str])] = &[
    ("dekart/dekart.zippel", &["n=3", "b=2", "l_chunk=8"]),
    ("membership/membership.zippel", &["N=2", "M=2", "S=2"]),
    ("zk_kzg/zk_kzg.zippel", &["N=2"]),
];

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples")
}

fn zippel_examples() -> Vec<PathBuf> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(examples_dir()).unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        for file in std::fs::read_dir(&dir).unwrap() {
            let file = file.unwrap().path();
            if file.extension().is_some_and(|e| e == "zippel") {
                files.push(file);
            }
        }
    }
    files.sort();
    files
}

fn zippel_check(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_zippel-check"))
        .args(args)
        .output()
        .expect("failed to run zippel-check")
}

fn relative(path: &Path) -> String {
    path.strip_prefix(examples_dir())
        .unwrap()
        .to_string_lossy()
        .replace('\\', "/")
}

#[test]
fn all_examples_pass() {
    let examples = zippel_examples();
    assert!(!examples.is_empty(), "no examples found");

    let mut failures = Vec::new();
    for path in &examples {
        let name = relative(path);
        let sizes = EXAMPLE_SIZES
            .iter()
            .find(|(file, _)| *file == name)
            .map_or(&[][..], |(_, sizes)| *sizes);
        let mut args: Vec<&str> = sizes.iter().flat_map(|s| ["--size", s]).collect();
        let path_str = path.to_str().unwrap();
        args.push(path_str);
        let out = zippel_check(&args);
        if !out.status.success() {
            failures.push(format!("{name}:\n{}", String::from_utf8_lossy(&out.stderr)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} examples failed zippel-check:\n\n{}",
        failures.len(),
        examples.len(),
        failures.join("\n")
    );
}

#[test]
fn size_listed_examples_fail_at_default_sizes() {
    // Guards `EXAMPLE_SIZES` against going stale: drop an entry once its example passes at
    // default sizes.
    for (name, _) in EXAMPLE_SIZES {
        let path = examples_dir().join(name);
        let out = zippel_check(&[path.to_str().unwrap()]);
        assert_eq!(
            out.status.code(),
            Some(1),
            "{name} now passes at default sizes; remove it from EXAMPLE_SIZES"
        );
    }
}

#[test]
fn type_error_reports_location_and_fails() {
    let dir = tempdir();
    let path = dir.join("bad.zippel");
    std::fs::write(
        &path,
        "proto bad<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {\n    u <- g * x;\n    verify(x + g == u)\n}\n",
    )
    .unwrap();
    let out = zippel_check(&[path.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("bad.zippel:3:12"), "{stderr}");
    assert!(stderr.contains("LubError"), "{stderr}");
    assert!(
        !stderr.contains('\x1b'),
        "colors must be off when not a terminal"
    );
    assert!(String::from_utf8_lossy(&out.stdout).contains("1 error"));
}

/// Check `src` as `<name>.zippel` and return the exit code and stderr.
fn check_program(name: &str, src: &str) -> (Option<i32>, String) {
    let path = tempdir().join(format!("{name}.zippel"));
    std::fs::write(&path, src).unwrap();
    let out = zippel_check(&[path.to_str().unwrap()]);
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

// These are well-typed but fail `ZippelHandler::compile`; zippel-check must catch them too.

#[test]
fn witness_in_verifier_is_reported_at_the_witness() {
    let (code, stderr) = check_program(
        "witness_leak",
        "proto leak<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {\n    verify(g * x == h)\n}\n",
    );
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("the verifier depends on witness `x`"),
        "{stderr}"
    );
    assert!(stderr.contains("witness_leak.zippel:1:44"), "{stderr}");
}

#[test]
fn random_in_verifier_is_reported_at_the_sample() {
    let (code, stderr) = check_program(
        "random_leak",
        "proto leak<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {\n    let r = random<F>;\n    u <- g * r;\n    c <- challenge<F*>;\n    z <- r + x * c;\n    verify(g * r == u)\n}\n",
    );
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("the verifier depends on random value `r`"),
        "{stderr}"
    );
    assert!(stderr.contains("random_leak.zippel:2:9"), "{stderr}");
}

#[test]
fn proto_without_verify_is_reported() {
    let (code, stderr) = check_program(
        "no_verify",
        "proto p<G: Group, F: Scalar<G>>(instance g: G) where g == g {\n    u <- g;\n}\n",
    );
    assert_eq!(code, Some(1), "{stderr}");
    assert!(stderr.contains("has no `verify` check"), "{stderr}");
}

#[test]
fn non_polynomial_fun_is_reported_at_the_operation() {
    let (code, stderr) = check_program(
        "nonpoly_fun",
        "proto np<F: Field>(instance a: F) where a == a {\n    let p = (fun(x) => x / a);\n    verify(p(a) == p(a))\n}\n",
    );
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("`fun` body is not a polynomial"),
        "{stderr}"
    );
    assert!(stderr.contains("nonpoly_fun.zippel:2:24"), "{stderr}");
}

#[test]
fn bad_usage_exits_with_2() {
    assert_eq!(zippel_check(&[]).status.code(), Some(2));
    assert_eq!(
        zippel_check(&["--size", "N", "x.zippel"]).status.code(),
        Some(2)
    );
    assert_eq!(
        zippel_check(&["--size", "N=-1", "x.zippel"]).status.code(),
        Some(2)
    );
    assert_eq!(
        zippel_check(&["--bogus", "x.zippel"]).status.code(),
        Some(2)
    );
}

#[test]
fn missing_file_fails() {
    let out = zippel_check(&["does/not/exist.zippel"]);
    assert_eq!(out.status.code(), Some(1));
}

/// A fresh directory under the target dir, so the test needs no extra dependencies.
fn tempdir() -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "zippel-check-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}
