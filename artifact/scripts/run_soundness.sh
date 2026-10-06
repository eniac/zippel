#!/usr/bin/env bash
# Experiment 2: special-soundness analysis across all nine candidates
# (analysis_all, Singular backend, 16 GiB memory limit per run).
#
# Runs every candidate, including the five the analysis cannot verify,
# and records statuses, failure reasons, timings and memory metrics.
# See ../README.md for the mapping to the paper's claim (§9.3).
#
# Usage:
#   artifact/scripts/run_soundness.sh [extra cargo-bench-analysis_all args...]
#
# Extra arguments are forwarded to analysis_all, e.g.
#   artifact/scripts/run_soundness.sh --protocols schnorr,okamoto
# analysis_all defaults to a 20-minute timeout; --timeout overrides it.
# process_soundness.py renders the JSON and checks expected outcomes.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

OUT_DIR="artifact/output"
mkdir -p "${OUT_DIR}"

echo "== Special-soundness analysis =="
cargo bench --bench analysis_all -- --analysis soundness \
    --output "${OUT_DIR}/soundness_results.json" \
    --log "${OUT_DIR}/soundness_all.log" \
    "$@"
