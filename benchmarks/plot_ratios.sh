#!/usr/bin/env bash
# Thin wrapper around plot_ratios.py: creates benchmarks/.venv on first run,
# installs matplotlib, then runs the plot script. Forwards any CLI args.
#
# Usage:
#   benchmarks/plot_ratios.sh                       # default csv/out-dir
#   benchmarks/plot_ratios.sh --csv path.csv --out-dir path/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")"
VENV="${SCRIPT_DIR}/.venv"
cd "${ROOT}"

if [[ ! -d "${VENV}" ]]; then
    echo ">>> creating venv at ${VENV}" >&2
    python3 -m venv "${VENV}"
fi

# shellcheck disable=SC1091
source "${VENV}/bin/activate"

if ! python3 -c "import matplotlib" >/dev/null 2>&1; then
    echo ">>> installing matplotlib into venv" >&2
    python3 -m pip install --quiet --disable-pip-version-check matplotlib
fi

python3 "${SCRIPT_DIR}/plot_ratios.py" "$@"
