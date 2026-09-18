#!/usr/bin/env bash
# Quick sanity check that the artifact image is set up correctly: prints
# the toolchain versions, runs a handful of protocol examples end to end,
# runs one completeness-analysis trial through Singular, and runs the
# `inline` bench binary on one small protocol. This is NOT one of the
# three paper experiments (see run_soundness.sh / run_benchmark.sh /
# run_completeness.sh for those). It's meant to finish in well under a
# minute and catch a broken environment before a reviewer commits to a
# full run.
#
# Usage: artifact/scripts/smoke_test.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

echo "== Toolchain =="
rustc --version
cargo --version
Singular --version | head -1
echo

echo "== Running example protocols =="
for proto in schnorr kzg ipa; do
    echo "-- ${proto} --"
    cargo run --release --example zippel -- "${proto}"
    echo
done

echo "== Completeness analysis (Singular) on schnorr =="
cargo test -p analyses --test gb_snapshots --release -- --exact 'completeness::schnorr'
echo

echo "== inline bench binary on schnorr (Singular backend) =="
cargo bench --bench inline -- --backend singular schnorr
echo

echo "Smoke test passed."
