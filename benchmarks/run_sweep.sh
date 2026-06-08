#!/usr/bin/env bash
# Sweep all protocol benches over thread counts {1, 2, 4} and emit one CSV.
#
# Drives `bench_all`, which already iterates each system over a sensible size
# grid (system-specific caps; see bench_all.rs for the per-system grids). For
# each thread count we re-launch bench_all with RAYON_NUM_THREADS set — varying
# threads in-process via rayon::install hangs arkworks' `parallel` feature,
# so the wrapper approach is the only reliable path.
#
# Usage:
#   ./run_sweep.sh                       # all systems, threads 1 2 4, full grid
#   ./run_sweep.sh --quick               # tiny grid for smoke-testing
#   ./run_sweep.sh --systems pst13,hyrax # subset
#   ./run_sweep.sh --threads 1,4         # custom thread sweep
#   ./run_sweep.sh --out /path/to.csv    # output path (default: ./sweep.csv)
#
# Notes:
#   - Builds bench_all in release once. Skip rebuild with --no-build.
#   - Each row in the CSV is one (system, threads, log_size) triple with
#     prove_ms, verify_ms, native_prove_ms, native_verify_ms.
#   - RUST_MIN_STACK=536870912 is set to survive deep rayon work-stealing at
#     large M (Spartan, PST13, etc. push past the default 8MB stack).

set -euo pipefail

# Resolve script dir so the script works regardless of where it's invoked from.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# Bench wrappers hard-code `examples/<system>/<proto>.zippel` as a path
# relative to CWD. Those files live at the workspace root, not under
# benchmarks/, so we run from the workspace root.
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

OUT="${SCRIPT_DIR}/sweep.csv"
THREADS_LIST="1,2,4"
SYSTEMS=""
QUICK_FLAG=""
BUILD=1
EXTRA_ARGS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --out)
            OUT="$2"
            shift 2
            ;;
        --threads)
            THREADS_LIST="$2"
            shift 2
            ;;
        --systems)
            SYSTEMS="$2"
            shift 2
            ;;
        --quick)
            QUICK_FLAG="--quick"
            shift
            ;;
        --no-build)
            BUILD=0
            shift
            ;;
        --)
            shift
            EXTRA_ARGS+=("$@")
            break
            ;;
        *)
            echo "unknown arg: $1" >&2
            exit 2
            ;;
    esac
done

BIN="${SCRIPT_DIR}/target/release/bench_all"

if [[ $BUILD -eq 1 ]]; then
    echo "[build] cargo build --release --bin bench_all"
    (cd "$SCRIPT_DIR" && cargo build --release --bin bench_all)
fi

if [[ ! -x "$BIN" ]]; then
    echo "missing bench_all binary at $BIN; run without --no-build" >&2
    exit 1
fi

# Resolve OUT to an absolute path BEFORE cd-ing into the workspace root, so a
# relative --out resolves against the user's CWD, not the workspace root.
case "$OUT" in
    /*) ;;
    *) OUT="$(pwd)/$OUT" ;;
esac

# Reset output file so a re-run doesn't append onto stale data.
: > "$OUT"

IFS=',' read -ra THREADS <<< "$THREADS_LIST"

export RUST_MIN_STACK=536870912

FIRST=1
for T in "${THREADS[@]}"; do
    echo
    echo "============================================================"
    echo "  threads = $T"
    echo "============================================================"

    # Write directly to the final CSV — bench_all flushes per-row, so a
    # Ctrl+C mid-iteration leaves a usable partial CSV.
    args=(--out "$OUT" --threads-label "$T")
    if [[ -n "$SYSTEMS" ]]; then
        args+=(--systems "$SYSTEMS")
    fi
    if [[ -n "$QUICK_FLAG" ]]; then
        args+=("$QUICK_FLAG")
    fi
    if [[ $FIRST -eq 0 ]]; then
        args+=(--no-header)
    fi

    ( cd "$WORKSPACE_ROOT" && RAYON_NUM_THREADS="$T" "$BIN" "${args[@]}" ${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"} )

    FIRST=0
done

echo
echo "=== done ==="
echo "wrote: $OUT"
wc -l "$OUT"
