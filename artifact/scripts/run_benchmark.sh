#!/usr/bin/env bash
# Experiment 1: cross-protocol performance benchmark (zippel-compiled
# protocols vs. hand-optimized native baselines).
#
# Wraps benchmarks/run_all.sh, defaulting to all 9 systems the paper
# reports at each system's paper-reported instance size (log_size=18,
# fixed for Schnorr -- run_all.sh's own default grid), threads {1,2,4,8}.
# Maps to Figure 7 of the submitted paper (page 13) -- see ../README.md.
#
# Override SYSTEMS/THREADS/PROVER_SAMPLES/OUT/QUICK via environment
# variables (forwarded to run_all.sh, see benchmarks/README.md) to narrow
# scope, e.g. to smoke-test this script itself without paying for the
# full sweep:
#   SYSTEMS=schnorr,kzg THREADS=1,2 artifact/scripts/run_benchmark.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

SYSTEMS="${SYSTEMS:-schnorr,sumcheck,ipa,kzg,pari,groth16,pst13,hyrax,spartan}"
THREADS="${THREADS:-1,2,4,8}"
OUT="${OUT:-artifact/output/bench_results.csv}"

mkdir -p "$(dirname "${OUT}")"

echo "== Benchmark: SYSTEMS=${SYSTEMS} THREADS=${THREADS} OUT=${OUT} =="
SYSTEMS="${SYSTEMS}" THREADS="${THREADS}" OUT="${OUT}" benchmarks/run_all.sh
