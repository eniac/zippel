#!/usr/bin/env bash
# Defensive sweep: runs each (system, threads) pair as its own bench_all
# subprocess with a per-pair timeout. A hang or crash in one combination
# only loses that combination — the rest of the sweep continues.
#
# Usage:
#   ./run_sweep_safe.sh                                   # all systems × {1,2,4} threads
#   ./run_sweep_safe.sh --threads 8,16,32,64              # custom threads
#   ./run_sweep_safe.sh --systems ipa,kzg --threads 1     # subset
#   ./run_sweep_safe.sh --timeout 1200 --out big.csv      # 20-min cap per pair
#   ./run_sweep_safe.sh --quick                           # tiny size grid

set -uo pipefail   # no -e: we want to continue on failure

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

OUT="${SCRIPT_DIR}/sweep.csv"
THREADS_LIST="1,2,4"
SYSTEMS_LIST="schnorr,sumcheck,ipa,kzg,pari,groth16,pst13,hyrax,spartan"
TIMEOUT_SECS=1800
QUICK_FLAG=""
BUILD=1

while [[ $# -gt 0 ]]; do
    case "$1" in
        --out)      OUT="$2"; shift 2 ;;
        --threads)  THREADS_LIST="$2"; shift 2 ;;
        --systems)  SYSTEMS_LIST="$2"; shift 2 ;;
        --timeout)  TIMEOUT_SECS="$2"; shift 2 ;;
        --quick)    QUICK_FLAG="--quick"; shift ;;
        --no-build) BUILD=0; shift ;;
        *) echo "unknown arg: $1" >&2; exit 2 ;;
    esac
done

BIN="${WORKSPACE_ROOT}/target/release/bench_all"

if [[ $BUILD -eq 1 ]]; then
    echo "[build] cargo build --release -p benchmarks --bin bench_all"
    (cd "$WORKSPACE_ROOT" && cargo build --release -p benchmarks --bin bench_all) || exit 1
fi

[[ -x "$BIN" ]] || { echo "missing $BIN" >&2; exit 1; }

# Absolute OUT path before any cd
case "$OUT" in /*) ;; *) OUT="$(pwd)/$OUT" ;; esac

# Reset output, write the header once.
: > "$OUT"
echo 'system,threads,log_size,prover_time_ms,verifier_time_ms,native_prover_time_ms,native_verifier_time_ms,zippel_ncloc,native_ncloc' > "$OUT"

export RUST_MIN_STACK=536870912

IFS=',' read -ra THREADS <<< "$THREADS_LIST"
IFS=',' read -ra SYSTEMS <<< "$SYSTEMS_LIST"

# Pick a timeout command — GNU coreutils on Linux, gtimeout on macOS via brew.
TIMEOUT_BIN="timeout"
command -v "$TIMEOUT_BIN" >/dev/null || TIMEOUT_BIN="gtimeout"
command -v "$TIMEOUT_BIN" >/dev/null || { echo "neither timeout nor gtimeout found" >&2; exit 1; }

for T in "${THREADS[@]}"; do
    for SYS in "${SYSTEMS[@]}"; do
        echo
        echo "==================== threads=$T system=$SYS ===================="

        TMP_CSV="$(mktemp)"
        # --no-header so bench_all doesn't re-emit the column header.
        # We pipe its row writes into TMP_CSV via --out, then concat.
        (
            cd "$WORKSPACE_ROOT" || exit 1
            RAYON_NUM_THREADS="$T" "$TIMEOUT_BIN" --signal=KILL "$TIMEOUT_SECS" \
                "$BIN" \
                --systems "$SYS" \
                --threads-label "$T" \
                --out "$TMP_CSV" \
                --no-header \
                $QUICK_FLAG
        )
        RC=$?

        if [[ $RC -eq 0 ]]; then
            cat "$TMP_CSV" >> "$OUT"
            ROWS=$(wc -l < "$TMP_CSV" | tr -d ' ')
            echo "  [ok]   $ROWS rows appended"
        elif [[ $RC -eq 124 || $RC -eq 137 ]]; then
            # Timeout (124) or SIGKILL (137 = 128+9). bench_all writes per-row,
            # so partial results in TMP_CSV are still valid.
            if [[ -s "$TMP_CSV" ]]; then
                cat "$TMP_CSV" >> "$OUT"
                ROWS=$(wc -l < "$TMP_CSV" | tr -d ' ')
                echo "  [timeout after ${TIMEOUT_SECS}s] $ROWS partial rows appended"
            else
                echo "  [timeout after ${TIMEOUT_SECS}s] no rows produced"
            fi
        else
            if [[ -s "$TMP_CSV" ]]; then
                cat "$TMP_CSV" >> "$OUT"
                ROWS=$(wc -l < "$TMP_CSV" | tr -d ' ')
                echo "  [exit=$RC] $ROWS partial rows appended"
            else
                echo "  [exit=$RC] no rows produced — moving on"
            fi
        fi
        rm -f "$TMP_CSV"
    done
done

echo
echo "=== done ==="
echo "wrote: $OUT"
wc -l "$OUT"
