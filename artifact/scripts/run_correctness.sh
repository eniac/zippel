#!/usr/bin/env bash
# Experiment 2: special-soundness correctness suite
# (analyses/tests/gb_snapshots, Singular backend).
#
# This reproduces the submitted paper's special-soundness claim (§9.3):
# it asserts that the special-soundness analysis actually succeeds, not
# merely that the code compiles, and snapshots the computed Groebner
# basis for regression detection. See ../README.md for the full mapping.
#
# Usage:
#   artifact/scripts/run_correctness.sh [FILTER]
#
# Defaults to the `soundness::*` trials. FILTER (optional) is forwarded
# as libtest-mimic's substring test-name filter and overrides this, e.g.
# `soundness::okamoto` to run a single trial. The summary below always
# reports soundness counts.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

FILTER="${1:-soundness::}"

LOG="$(mktemp)"
trap 'rm -f "${LOG}"' EXIT

echo "== Special-soundness correctness suite (analyses/tests/gb_snapshots) =="
set +e
cargo test -p analyses --test gb_snapshots --release -- "${FILTER}" 2>&1 | tee "${LOG}"
STATUS="${PIPESTATUS[0]}"
set -e

echo
echo "== Summary =="
pass=$(grep -c "^test soundness::.* \.\.\. ok$" "${LOG}" || true)
ignored=$(grep -c "^test soundness::.* \.\.\. ignored$" "${LOG}" || true)
failed=$(grep -c "^test soundness::.* \.\.\. FAILED$" "${LOG}" || true)
printf "soundness pass=%-3s ignored=%-3s failed=%-3s\n" "${pass}" "${ignored}" "${failed}"

exit "${STATUS}"
