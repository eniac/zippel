#!/usr/bin/env bash
# Experiment 1: cross-protocol performance benchmark (zippel-compiled
# protocols vs. hand-optimized native baselines).
#
# Wraps benchmarks/run_all.sh. By default it runs every system bench_all
# knows (its ALL_SYSTEMS: the paper's Figure 7 systems plus those added
# since) at run_all.sh's default size grid (log_size=18, fixed for
# Schnorr), threads {1,2,4,8}, and one sample per measurement
# (BENCH_SAMPLES=1). The pinned results in benchmarks/*_results.csv use
# BENCH_SAMPLES=10, which takes roughly ten times as long.
# Maps to Figure 7 of the submitted paper (page 13) -- see ../README.md.
#
# Override SYSTEMS/THREADS/BENCH_SAMPLES/OUT/QUICK via environment
# variables (forwarded to run_all.sh, see benchmarks/README.md) to narrow
# scope, e.g. to smoke-test this script itself without paying for the
# full sweep:
#   SYSTEMS=schnorr,kzg THREADS=1,2 artifact/scripts/run_benchmark.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

# Empty means every system bench_all knows.
SYSTEMS="${SYSTEMS:-}"
THREADS="${THREADS:-1,2,4,8}"
BENCH_SAMPLES="${BENCH_SAMPLES:-1}"
OUT="${OUT:-artifact/output/bench_results.csv}"

mkdir -p "$(dirname "${OUT}")"

echo "== Benchmark: SYSTEMS=${SYSTEMS:-all} THREADS=${THREADS} BENCH_SAMPLES=${BENCH_SAMPLES} OUT=${OUT} =="
SYSTEMS="${SYSTEMS}" THREADS="${THREADS}" BENCH_SAMPLES="${BENCH_SAMPLES}" OUT="${OUT}" \
    benchmarks/run_all.sh
