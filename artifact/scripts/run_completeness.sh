#!/usr/bin/env bash
# Experiment 3: completeness analysis across all 30 protocols (Singular
# backend, 20-minute per-run timeout, 16GiB memory limit, both inline
# and no-inline variants per protocol, by default -- inline_all's own
# defaults).
#
# Produces a supplementary table not present in the submitted paper (see
# ../README.md) and maps to Section 9.3 of the submitted paper's
# prose-only completeness-coverage claim ("Zippel can automatically
# verify N of them").
#
# Usage:
#   artifact/scripts/run_completeness.sh [extra cargo-bench-inline_all args...]
#
# Any extra arguments are forwarded to `cargo bench --bench inline_all --`
# verbatim (it already accepts --timeout/--protocols/--memory-limit-mb/
# --inline-only). ../README.md's Experiment 3 uses
# `--inline-only --timeout 60`, since every protocol that completes does
# so in well under 60s and the no-inline variant is not part of the
# paper's claim; to smoke-test this script itself on a few protocols:
#   artifact/scripts/run_completeness.sh --inline-only --timeout 60 --protocols schnorr,groth16

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

OUT_DIR="artifact/output"
mkdir -p "${OUT_DIR}"

echo "== Completeness analysis =="
cargo bench --bench inline_all -- \
    --output "${OUT_DIR}/inline_results.json" \
    --log "${OUT_DIR}/inline_all.log" \
    "$@"
