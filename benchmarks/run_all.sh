#!/usr/bin/env bash
# Run every benchmark (schnorr, sumcheck, ipa, kzg, pari) across a set of
# thread counts and emit a single CSV.
#
# Threads are swept by re-running the binary with different RAYON_NUM_THREADS:
# in-process pool reconfiguration via rayon::ThreadPool::install hangs on
# arkworks' parallel path for our protocols.
#
# Usage:
#   benchmarks/run_all.sh                       # default: all systems × threads=1,2,4,8,16
#                                               # × max-size grid → bench_results.csv
#   THREADS="1,4" benchmarks/run_all.sh         # narrower thread sweep
#   OUT=results.csv benchmarks/run_all.sh
#   QUICK=1 benchmarks/run_all.sh               # small grid for iteration
#   SYSTEMS=kzg,pari benchmarks/run_all.sh      # filter systems

set -euo pipefail

THREADS="${THREADS:-1,2,4,8,16}"
OUT="${OUT:-bench_results.csv}"
QUICK="${QUICK:-0}"
SYSTEMS="${SYSTEMS:-}"

# Locate the workspace root (the dir containing this script's parent).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")"
cd "${ROOT}"

echo ">>> building bench_all (release)" >&2
# `benchmarks` is excluded from the workspace (Cargo.toml note explains why),
# so `-p benchmarks` from the root fails. Build from the crate's own manifest.
cargo build --release --manifest-path "${SCRIPT_DIR}/Cargo.toml" --bin bench_all >&2

BIN="${SCRIPT_DIR}/target/release/bench_all"

CHILD_ARGS=()
[[ "${QUICK}" == "1" ]] && CHILD_ARGS+=(--quick)
[[ -n "${SYSTEMS}" ]] && CHILD_ARGS+=(--systems "${SYSTEMS}")

IFS=',' read -r -a THREAD_LIST <<< "${THREADS}"

# Each thread iteration writes DIRECTLY to OUT (append mode). bench_all
# flushes per row, so Ctrl-C anywhere — between threads, mid-iteration
# within a system, or between systems — preserves every row that finished
# before the interrupt. The first call writes the header and truncates;
# subsequent calls append with --no-header --append.
HEADER_DONE=0
: > "${OUT}"
for T in "${THREAD_LIST[@]}"; do
    EXTRA=()
    if [[ "${HEADER_DONE}" == "1" ]]; then
        EXTRA+=(--no-header --append)
    fi
    echo ">>> threads=${T}" >&2
    RAYON_NUM_THREADS="${T}" "${BIN}" \
        --out "${OUT}" \
        --threads-label "${T}" \
        ${CHILD_ARGS[@]+"${CHILD_ARGS[@]}"} \
        ${EXTRA[@]+"${EXTRA[@]}"}
    HEADER_DONE=1
done

ROWS=$(($(wc -l < "${OUT}") - 1))
echo ">>> done — ${ROWS} rows in ${OUT}" >&2
