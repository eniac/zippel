#!/usr/bin/env python3
"""Report non-comment source line counts (NCLOC) for the 30+ protocols the
paper implements (its Figure 6, the "List of proof systems implemented
in Zippel" table).
This is broader than run_benchmark.sh's LoC columns,
which only cover the systems that also have a native baseline to compare
against (the paper's Figure 7).

NCLOC rule matches benchmarks/src/bin/bench_all.rs's
`count_ncloc_line_comments`: a line counts if it is non-empty after
trimming and does not start with `//`.

These numbers will not match the submitted paper's Figure 6 for most
protocols. Two things changed since submission: `zippel-fmt` did not
exist yet, so the example files were not written in its canonical style
and reformatting them afterward moved line counts on its own, and several
protocols' `where`-clause constraints were revised afterward (see the
completeness-count accounting in ../README.md's Experiment 3 section).
Both change line counts independently of each other. See ../README.md's
Experiment 1 section for why this doesn't undercut the paper's
conciseness claim.

Needs no build, no Docker: just reads the .zippel source files directly.
Run from the repo root:

    python3 artifact/scripts/report_loc.py

The protocols are the paper's Figure 6 rows, in order, from paper.py.
"""

from pathlib import Path

from paper import FIGURE_6


def ncloc(path: Path) -> int:
    count = 0
    for line in path.read_text().splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("//"):
            count += 1
    return count


def main():
    repo_root = Path(__file__).resolve().parents[2]
    print("| Proof System | LoC |")
    print("|---|---|")
    total = 0
    for _, label, example, *_ in FIGURE_6:
        loc = ncloc(repo_root / "examples" / example / f"{example}.zippel")
        total += loc
        print(f"| {label} | {loc} |")
    print()
    print(f"{len(FIGURE_6)} protocols, {total} lines total.")


if __name__ == "__main__":
    main()
