use std::process::Command;

const KNOWN_GOOD_EXAMPLES: &[&str] = &[
    "schnorr",
    "kzg",
    "mle",
    "zerocheck",
    // "marginalize", // TODO(Phase 4): parses/compiles/proves, but static analysis still
    // panics at graph/src/analyses/groebner/mod.rs:2584 while the known marginalize
    // next_poly/dynamic-round dependency is completed.
];

#[test]
fn documented_examples_exit_successfully() {
    for &example in KNOWN_GOOD_EXAMPLES {
        let output = Command::new(env!("CARGO"))
            .args(["run", "--quiet", "--example", example])
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .output()
            .unwrap_or_else(|err| panic!("failed to run cargo example `{example}`: {err}"));

        assert!(
            output.status.success(),
            "example `{example}` exited with status {:?}\n\nstdout:\n{}\n\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }
}
