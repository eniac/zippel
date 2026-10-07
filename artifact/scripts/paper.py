#!/usr/bin/env python3
"""The paper's Figure 6 ("List of proof systems implemented in Zippel")
and Figure 7 (comparison with existing implementations): the protocols
the artifact reports on. benches/ and benchmarks/ cover every
implemented protocol; the artifact scripts only run and report the ones
below.

FIGURE_7 rows: label, bench_all system, bench_all baseline.

FIGURE_6 rows: year, label, example, analysis protocol, Comp. mark, Sound. mark.
`example` names examples/<example>/<example>.zippel (its line count is the
LoC column). `analysis` is the protocol name registered in
benches/analysis/protocols.rs; Dory IPA's "~" mark means the analysis
confirms it only at a smaller instance, `dory_ipa_s2`. Marks are "✓",
"✗", "~", or None for a protocol that column does not report on.

Usage:
    python3 artifact/scripts/paper.py completeness|soundness

prints the comma-separated analysis protocols for that column.
"""

import sys

OK, NO, PARTIAL = "✓", "✗", "~"

FIGURE_6 = [
    (1990, "Sumcheck", "sumcheck", "sumcheck", OK, None),
    (1991, "Schnorr", "schnorr", "schnorr", OK, OK),
    (1991, "Multi-Schnorr", "schnorr_3round", "schnorr_3round", OK, OK),
    (1992, "Okamoto", "okamoto", "okamoto", OK, NO),
    (1992, "ElGamal", "okamoto_elgamal", "okamoto_elgamal", OK, OK),
    (1993, "Chaum-Pedersen", "cp", "cp", OK, OK),
    (1994, "CDS Disjunction", "cds", "cds", OK, NO),
    (2009, "Hadamard", "hadamard", "hadamard", OK, None),
    (2010, "E-Cash Coin", "coin_proof", "coin_proof", OK, NO),
    (2010, "KZG", "kzg", "kzg", OK, None),
    (2013, "MLE Sum", "mle_sumcheck", "mle_sumcheck", OK, None),
    (2013, "PST13", "pst13", "pst13", OK, None),
    (2016, "BCCGP IPA", "bccgp", "bccgp", OK, None),
    (2016, "Groth16", "groth16", "groth16", OK, None),
    (2018, "Bulletproofs", "ipa", "ipa", OK, None),
    (2018, "Dot Product", "hyrax_podp", "hyrax_podp", OK, None),
    (2018, "Product Proof", "hyrax_pop", "hyrax_pop", OK, None),
    (2018, "Hyrax IPA", "hyrax_ipa", "hyrax_ipa", OK, None),
    (2018, "Hyrax PCS", "hyrax_pcs", "hyrax_pcs", OK, None),
    (2020, "Membership", "membership", "membership", OK, None),
    (2020, "Marlin-KZG", "marlin_kzg", "marlin_kzg", OK, None),
    (2020, "Spartan", "spartan", "spartan", NO, None),
    (2021, "Dory IPA", "dory_ipa", "dory_ipa_s2", PARTIAL, None),
    (2021, "Dory PCS", "dory_pcs", "dory_pcs", OK, None),
    (2021, "R1CS Σ", "r1cs_sigma", "r1cs_sigma", OK, None),
    (2023, "Multiset", "hyperplonk_multiset", "hyperplonk_multiset", OK, None),
    (2023, "Permutation", "hyperplonk_permutation", "hyperplonk_permutation", NO, None),
    (2023, "Zerocheck", "hyperplonk_zerocheck", "hyperplonk_zerocheck", OK, None),
    (2023, "Product-Check", "hyperplonk_productcheck", "hyperplonk_productcheck", OK, None),
    (2023, "HyperPlonk", "hyperplonk_snark", "hyperplonk_snark", NO, None),
    (2024, "Zeromorph-KZG", "zeromorph_kzg", "zeromorph_kzg", OK, None),
    (2025, "KZH", "kzh", "kzh", OK, None),
    (2025, "Dekart", "dekart", "dekart", NO, None),
    (2026, "Pari", "pari", "pari", NO, None),
]

COLUMNS = {"completeness": 4, "soundness": 5}

# The paper's Figure 7 (comparison with existing implementations), in its
# row order: label, bench_all system, bench_all baseline.
FIGURE_7 = [
    ("Sumcheck", "sumcheck", "sumcheck"),
    ("Schnorr", "schnorr", "schnorr"),
    ("KZG", "kzg", "kzg"),
    ("PST13", "pst13", "pst13"),
    ("Groth16", "groth16", "groth16"),
    ("Bulletproofs", "ipa", "ipa"),
    ("Hyrax", "hyrax", "hyrax"),
    ("Spartan (Arkworks)", "spartan", "ark-spartan"),
    ("Spartan (Microsoft)", "spartan", "spartan"),
    ("Dory PCS", "dory", "dory"),
    ("HyperPlonk", "hyperplonk", "hyperplonk"),
    ("KZH", "kzh", "kzh"),
    ("DeKART", "dekart", "dekart"),
    ("Pari", "pari", "pari"),
]


def rows(column):
    """The Figure 6 rows that `column` ("completeness" or "soundness")
    reports a mark for, as (label, analysis protocol, mark)."""
    i = COLUMNS[column]
    return [(r[1], r[3], r[i]) for r in FIGURE_6 if r[i] is not None]


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in COLUMNS:
        sys.exit(__doc__)
    print(",".join(protocol for _, protocol, _ in rows(sys.argv[1])))
