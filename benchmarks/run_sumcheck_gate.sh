#!/usr/bin/env bash
# Sumcheck benchmark gate convenience wrapper.
#
# Captures one subprocess per requested Rayon thread count, then merges the
# validated single-thread artifacts into the declared matrix.
#
# Usage:
#   benchmarks/run_sumcheck_gate.sh capture \
#     --out target/sumcheck-baseline.json \
#     --threads 1,4 \
#     --num-vars 4,8 \
#     --max-degree 3 \
#     --repeats 3 \
#     --seed 0x5eed5eed

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MANIFEST="$SCRIPT_DIR/Cargo.toml"

usage() {
    cat >&2 <<'USAGE'
Usage:
  run_sumcheck_gate.sh capture --out PATH [options]

Options:
  --threads LIST       Comma-separated Rayon thread counts (default: 1)
  --num-vars GRID      Comma-separated values/ranges, e.g. 4,8 or 3..20 (default: 4,8,12)
  --max-degree GRID    Comma-separated values/ranges (default: 3)
  --repeats N          Measured samples per case (default: 7)
  --warmups N          Warmup samples per case (default: 1)
  --seed SEED          Decimal or hex seed (default: 0x5eed5eed)
  --source-path PATH   Zippel sumcheck source path (default: examples/sumcheck/sumcheck.zippel)
  --allow-large-cases  Forwarded to sumcheck_gate capture
  --release-bin        Use cargo run --release (default; kept for readability)
USAGE
}

[[ $# -gt 0 ]] || { usage; exit 2; }
COMMAND="$1"
shift
[[ "$COMMAND" == "capture" ]] || { echo "unknown command: $COMMAND" >&2; usage; exit 2; }

OUT=""
THREADS="1"
NUM_VARS="4,8,12"
MAX_DEGREE="3"
REPEATS="7"
WARMUPS="1"
SEED="0x5eed5eed"
SOURCE_PATH="examples/sumcheck/sumcheck.zippel"
ALLOW_LARGE=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --out) OUT="$2"; shift 2 ;;
        --threads) THREADS="$2"; shift 2 ;;
        --num-vars) NUM_VARS="$2"; shift 2 ;;
        --max-degree) MAX_DEGREE="$2"; shift 2 ;;
        --repeats) REPEATS="$2"; shift 2 ;;
        --warmups) WARMUPS="$2"; shift 2 ;;
        --seed) SEED="$2"; shift 2 ;;
        --source-path) SOURCE_PATH="$2"; shift 2 ;;
        --allow-large-cases) ALLOW_LARGE=1; shift ;;
        --release-bin) shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "unknown arg: $1" >&2; usage; exit 2 ;;
    esac
done

[[ -n "$OUT" ]] || { echo "--out is required" >&2; usage; exit 2; }

case "$OUT" in
    /*) ;;
    [A-Za-z]:*) ;;
    *) OUT="$REPO_ROOT/$OUT" ;;
esac

PART_DIR="${OUT}.parts"
mkdir -p "$PART_DIR"

IFS=',' read -ra THREAD_ARRAY <<< "$THREADS"
PARTS=()
for raw_thread in "${THREAD_ARRAY[@]}"; do
    THREAD="$(echo "$raw_thread" | tr -d '[:space:]')"
    [[ -n "$THREAD" ]] || { echo "empty thread entry in --threads" >&2; exit 2; }
    PART="$PART_DIR/thread-${THREAD}.json"
    echo "[capture] RAYON_NUM_THREADS=$THREAD -> $PART"
    CAPTURE_ARGS=(
        run --release --manifest-path "$MANIFEST" --bin sumcheck_gate -- capture
        --out "$PART"
        --threads-label "$THREAD"
        --num-vars "$NUM_VARS"
        --max-degree "$MAX_DEGREE"
        --repeats "$REPEATS"
        --warmups "$WARMUPS"
        --seed "$SEED"
        --source-path "$SOURCE_PATH"
    )
    if [[ $ALLOW_LARGE -eq 1 ]]; then
        CAPTURE_ARGS+=(--allow-large-cases)
    fi
    (cd "$REPO_ROOT" && RAYON_NUM_THREADS="$THREAD" cargo "${CAPTURE_ARGS[@]}")
    PARTS+=("$PART")
done

echo "[merge] -> $OUT"
(cd "$REPO_ROOT" && cargo run --release --manifest-path "$MANIFEST" --bin sumcheck_gate -- merge \
    --out "$OUT" \
    --num-vars "$NUM_VARS" \
    --max-degree "$MAX_DEGREE" \
    --threads "$THREADS" \
    "${PARTS[@]}")

echo "wrote: $OUT"
