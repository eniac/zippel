#!/usr/bin/env bash
# Experiment 3: inline vs. no-inline completeness-analysis sweep across
# all 30 protocols (Singular backend, 20-minute per-run timeout, 16GiB
# memory limit by default -- inline_all's own defaults).
#
# Produces a supplementary table not present in the submitted paper (see
# ../README.md) and maps to Section 9.3 of the submitted paper's
# prose-only completeness-coverage claim ("Zippel can automatically
# verify N of them").
#
# Usage:
#   artifact/scripts/run_inline.sh [extra cargo-bench-inline_all args...]
#
# Any extra arguments are forwarded to `cargo bench --bench inline_all --`
# verbatim (it already accepts --timeout/--protocols/--memory-limit-mb),
# so e.g. to smoke-test this script itself on a few protocols with a much
# shorter timeout instead of the full 30-protocol x 20-minute sweep:
#   artifact/scripts/run_inline.sh --timeout 60 --protocols schnorr,groth16

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

OUT_DIR="artifact/output"
mkdir -p "${OUT_DIR}"

echo "== Inline vs. no-inline completeness sweep =="
cargo bench --bench inline_all -- \
    --output "${OUT_DIR}/inline_results.json" \
    --log "${OUT_DIR}/inline_all.log" \
    "$@"
