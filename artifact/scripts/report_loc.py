#!/usr/bin/env python3
"""Report non-comment source line counts (NCLOC) for all 30 protocols the
paper implements (its Figure 6, the "List of proof systems implemented
in Zippel" table). This is broader than run_benchmark.sh's LoC columns,
which only cover the 9 systems that also have a native baseline to
compare against (the paper's Figure 7).

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

The protocol/path list below must be kept in sync with the `PROTOCOLS`
array in benches/inline/main.rs (the canonical list of the paper's 30
protocols).
"""

from pathlib import Path

PROTOCOLS = [
    ("sumcheck", "examples/sumcheck/sumcheck.zippel"),
    ("schnorr", "examples/schnorr/schnorr.zippel"),
    ("schnorr_3round", "examples/schnorr_3round/schnorr_3round.zippel"),
    ("okamoto", "examples/okamoto/okamoto.zippel"),
    ("cp", "examples/cp/cp.zippel"),
    ("cds", "examples/cds/cds.zippel"),
    ("hadamard", "examples/hadamard/hadamard.zippel"),
    ("coin_proof", "examples/coin_proof/coin_proof.zippel"),
    ("kzg", "examples/kzg/kzg.zippel"),
    ("mle_sumcheck", "examples/mle_sumcheck/mle_sumcheck.zippel"),
    ("pst13", "examples/pst13/pst13.zippel"),
    ("bccgp", "examples/bccgp/bccgp.zippel"),
    ("groth16", "examples/groth16/groth16.zippel"),
    ("ipa", "examples/ipa/ipa.zippel"),
    ("hyrax_podp", "examples/hyrax_podp/hyrax_podp.zippel"),
    ("hyrax_pop", "examples/hyrax_pop/hyrax_pop.zippel"),
    ("hyrax", "examples/hyrax_ipa/hyrax_ipa.zippel"),
    ("membership", "examples/membership/membership.zippel"),
    ("spartan", "examples/spartan/spartan.zippel"),
    ("dory", "examples/dory/dory.zippel"),
    ("r1cs_sigma", "examples/r1cs_sigma/r1cs_sigma.zippel"),
    ("hyperplonk_multiset", "examples/hyperplonk_multiset/hyperplonk_multiset.zippel"),
    (
        "hyperplonk_permutation",
        "examples/hyperplonk_permutation/hyperplonk_permutation.zippel",
    ),
    (
        "hyperplonk_zerocheck",
        "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel",
    ),
    (
        "hyperplonk_productcheck",
        "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel",
    ),
    ("hyperplonk", "examples/hyperplonk/hyperplonk.zippel"),
    ("zk_kzg", "examples/zk_kzg/zk_kzg.zippel"),
    ("kzh", "examples/kzh/kzh.zippel"),
    ("dekart", "examples/dekart/dekart.zippel"),
    ("pari", "examples/pari/pari.zippel"),
]


def ncloc(path: Path) -> int:
    count = 0
    for line in path.read_text().splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("//"):
            count += 1
    return count


def main():
    repo_root = Path(__file__).resolve().parents[2]
    print("| Protocol | LoC |")
    print("|---|---|")
    total = 0
    for name, rel_path in PROTOCOLS:
        loc = ncloc(repo_root / rel_path)
        total += loc
        print(f"| {name} | {loc} |")
    print()
    print(f"{len(PROTOCOLS)} protocols, {total} lines total.")


if __name__ == "__main__":
    main()
