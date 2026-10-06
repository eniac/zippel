#!/usr/bin/env bash
# Experiment 3: completeness analysis across all the paper's protocols 
# (Singular backend, 20-minute per-run timeout,
# 16GiB memory limit, by default -- analysis_all's own defaults).
#
# Produces a supplementary table not present in the submitted paper (see
# ../README.md) and maps to Section 9.3 of the submitted paper's
# prose-only completeness-coverage claim ("Zippel can automatically
# verify N of them").
#
# Usage:
#   artifact/scripts/run_completeness.sh [extra cargo-bench-analysis_all args...]
#
# Any extra arguments are forwarded to
# `cargo bench --bench analysis_all -- --analysis completeness` verbatim
# (it already accepts --timeout/--protocols/--memory-limit-mb).
# To smoke-test this script itself on a few protocols:
#   artifact/scripts/run_completeness.sh --timeout 60 --protocols schnorr,groth16

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

OUT_DIR="artifact/output"
mkdir -p "${OUT_DIR}"

echo "== Completeness analysis =="
# The paper's protocols (artifact/scripts/paper.py), unless the caller
# picks its own with --protocols.
PROTOCOLS=(--protocols "$(python3 "${SCRIPT_DIR}/paper.py" completeness)")
for arg in "$@"; do
    case "${arg}" in --protocols | --protocols=*) PROTOCOLS=() ;; esac
done

cargo bench --bench analysis_all -- --analysis completeness \
    --output "${OUT_DIR}/completeness_results.json" \
    --log "${OUT_DIR}/completeness_all.log" \
    "${PROTOCOLS[@]}" "$@"
