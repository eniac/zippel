//! Exposes the source directories of the external crates whose code is a
//! native baseline, so `bench_all` can `include_str!` and count them
//! instead of hard-coding their line counts. Each becomes a
//! `<NAME>_SRC_DIR` env var (e.g. `ARK_GROTH16_SRC_DIR`), pointing at
//! the exact version `Cargo.lock` resolved.

use std::env;
use std::path::Path;
use std::process::Command;

const CRATES: [&str; 4] = [
    "ark-crypto-primitives",
    "ark-poly-commit",
    "ark-groth16",
    "spartan",
];

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../Cargo.lock");

    let output = Command::new(env::var("CARGO").unwrap())
        .args([
            "metadata",
            "--format-version",
            "1",
            "--offline",
            "--manifest-path",
        ])
        .arg(Path::new(&manifest_dir).join("Cargo.toml"))
        .output()
        .expect("failed to run `cargo metadata`");
    assert!(
        output.status.success(),
        "`cargo metadata` failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let metadata: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let packages = metadata["packages"].as_array().unwrap();

    // `resolve.nodes` lists only packages actually in this build, so a
    // stale second version of a crate in the registry is never picked.
    let benchmarks_id = packages
        .iter()
        .find(|p| p["name"] == "benchmarks")
        .and_then(|p| p["id"].as_str())
        .unwrap();
    let deps = metadata["resolve"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["id"] == benchmarks_id)
        .unwrap()["deps"]
        .as_array()
        .unwrap();

    for name in CRATES {
        let dep_ids: Vec<&str> = deps
            .iter()
            .filter_map(|d| d["pkg"].as_str())
            .filter(|id| packages.iter().any(|p| p["id"] == *id && p["name"] == name))
            .collect();
        let id = match dep_ids.as_slice() {
            [id] => *id,
            _ => panic!("expected exactly one direct dependency named `{name}`"),
        };
        let manifest = packages.iter().find(|p| p["id"] == id).unwrap()["manifest_path"]
            .as_str()
            .unwrap();
        let dir = Path::new(manifest).parent().unwrap();
        let var = format!("{}_SRC_DIR", name.to_uppercase().replace('-', "_"));
        println!("cargo:rustc-env={var}={}", dir.display());
    }
}
