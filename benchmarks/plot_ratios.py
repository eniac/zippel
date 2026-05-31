#!/usr/bin/env python3
"""Plot zippel/native ratios per system from bench_results.csv.

For each system, emits one PDF containing 4 series:
  - prover ratio @ 1 thread   (blue, dashed)
  - prover ratio @ 4 threads  (blue, dash-dot)
  - verifier ratio @ 1 thread (red, dashed)
  - verifier ratio @ 4 threads (red, dash-dot)

X axis is the actual problem size (2 ** log_size), log-scaled.
Y axis is `zippel_time / native_time`, log-scaled and symmetric around 1
so the y=1 reference line lands at the visual center of the plot.

Usage:
  python3 benchmarks/plot_ratios.py                     # CSV: benchmarks/bench_results.csv, plots: benchmarks/plots/
  python3 benchmarks/plot_ratios.py --csv path.csv --out-dir path/
"""

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.ticker import LogFormatterMathtext, LogLocator, ScalarFormatter

# 1 thread vs 4 threads share color (per role: prover blue, verifier red)
# and differ by line style + marker.
THREAD_STYLE = {
    1: {"linestyle": "--", "marker": "o"},
    4: {"linestyle": "-.", "marker": "s"},
}
ROLE_COLOR = {"prover": "blue", "verifier": "red"}


def load(csv_path):
    rows = []
    with open(csv_path) as f:
        for r in csv.DictReader(f):
            rows.append(
                {
                    "system": r["system"],
                    "threads": int(r["threads"]),
                    "log_size": int(r["log_size"]),
                    "size": 1 << int(r["log_size"]),
                    "prove": float(r["prover_time_ms"]),
                    "verify": float(r["verifier_time_ms"]),
                    "n_prove": float(r["native_prover_time_ms"]),
                    "n_verify": float(r["native_verifier_time_ms"]),
                }
            )
    return rows


def plot_system(system, rows, out_dir):
    by_t = defaultdict(list)
    for r in rows:
        by_t[r["threads"]].append(r)
    for t in by_t:
        by_t[t].sort(key=lambda r: r["log_size"])

    fig, ax = plt.subplots(figsize=(8, 6))

    all_ratios = []
    for t, group in sorted(by_t.items()):
        if t not in THREAD_STYLE:
            continue
        style = THREAD_STYLE[t]
        xs = [r["size"] for r in group]
        prover_ratios = [r["prove"] / r["n_prove"] for r in group]
        verifier_ratios = [r["verify"] / r["n_verify"] for r in group]
        ax.plot(
            xs,
            prover_ratios,
            color=ROLE_COLOR["prover"],
            label=f"prover (t={t})",
            **style,
        )
        ax.plot(
            xs,
            verifier_ratios,
            color=ROLE_COLOR["verifier"],
            label=f"verifier (t={t})",
            **style,
        )
        all_ratios.extend(prover_ratios + verifier_ratios)

    # y=1 reference line (the only solid line in the figure).
    ax.axhline(1.0, color="black", linewidth=1.0)

    ax.set_xscale("log", base=2)
    ax.set_yscale("log")

    # Center y-axis on 1: pick a symmetric log range around 1 that covers
    # every observed ratio with ~20% padding on each side, so the y=1 line
    # is at the geometric center of the figure.
    if all_ratios:
        max_dev = max(max(r, 1.0 / r) for r in all_ratios if r > 0)
        max_dev = max(max_dev * 1.2, 1.05)
        ax.set_ylim(1.0 / max_dev, max_dev)

    ax.xaxis.set_major_locator(LogLocator(base=2.0))
    ax.xaxis.set_major_formatter(LogFormatterMathtext(base=2))
    # Show "1" instead of "10^0" on the y-axis (matplotlib defaults to
    # scientific notation under log scale).
    ax.yaxis.set_major_formatter(ScalarFormatter())
    ax.yaxis.set_minor_formatter(ScalarFormatter())
    ax.set_xlabel("size")
    ax.set_ylabel("zippel / native (lower is better)")
    ax.set_title(f"{system}: zippel vs native time ratio")
    ax.grid(True, which="both", linestyle=":", alpha=0.4)
    ax.legend(loc="best")

    out_path = out_dir / f"{system}_ratio.pdf"
    fig.tight_layout()
    fig.savefig(out_path)
    plt.close(fig)
    return out_path


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--csv", type=Path, default=Path("benchmarks/bench_results.csv"))
    p.add_argument("--out-dir", type=Path, default=Path("benchmarks/plots"))
    args = p.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = load(args.csv)
    by_sys = defaultdict(list)
    for r in rows:
        by_sys[r["system"]].append(r)

    for system in sorted(by_sys):
        path = plot_system(system, by_sys[system], args.out_dir)
        print(f"wrote {path}")


if __name__ == "__main__":
    main()
