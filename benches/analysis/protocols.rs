//! The protocols the `analysis` bench knows. `analysis_all` gets the ones
//! it sweeps from `analysis --list`.

/// Which analysis a run performs.
#[derive(Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum Analysis {
    /// `CompletenessAnalysis`.
    Completeness,
    /// `SpecialSoundnessAnalysis`.
    Soundness,
}

/// A registered protocol: its source, its sizes, and the analyses the sweep
/// runs on it.
pub struct Protocol {
    pub name: &'static str,
    pub path: &'static str,
    pub sizes: &'static [(&'static str, usize)],
    /// Whether the completeness sweep runs it: the paper's protocols.
    pub completeness: bool,
    /// The special-soundness round parameters, one per challenge round, for
    /// the protocols the soundness sweep runs: the paper's 6 special-sound
    /// candidates and 3 more Sigma protocols.
    pub soundness: Option<&'static [usize]>,
}

impl Protocol {
    /// Whether the sweep for `analysis` runs this protocol.
    pub const fn runs(&self, analysis: Analysis) -> bool {
        match analysis {
            Analysis::Completeness => self.completeness,
            Analysis::Soundness => self.soundness.is_some(),
        }
    }
}

/// The registered protocol called `name`.
pub fn find(name: &str) -> Option<&'static Protocol> {
    PROTOCOLS.iter().find(|p| p.name == name)
}

pub static PROTOCOLS: &[Protocol] = &[
    Protocol {
        name: "sumcheck",
        path: "examples/sumcheck/sumcheck_full.zippel",
        sizes: &[("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "schnorr",
        path: "examples/schnorr/schnorr.zippel",
        sizes: &[],
        completeness: true,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "schnorr_3round",
        path: "examples/schnorr_3round/schnorr_3round.zippel",
        sizes: &[],
        completeness: true,
        soundness: Some(&[2, 2, 2]),
    },
    Protocol {
        name: "okamoto",
        path: "examples/okamoto/okamoto.zippel",
        sizes: &[],
        completeness: true,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "cp",
        path: "examples/cp/cp.zippel",
        sizes: &[],
        completeness: true,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "cds",
        path: "examples/cds/cds.zippel",
        sizes: &[],
        completeness: true,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "hadamard",
        path: "examples/hadamard/hadamard.zippel",
        sizes: &[("S", 2)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "coin_proof",
        path: "examples/coin_proof/coin_proof.zippel",
        sizes: &[],
        completeness: true,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "kzg",
        path: "examples/kzg/kzg.zippel",
        sizes: &[("N", 2)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "mle_sumcheck",
        path: "examples/mle_sumcheck/mle_sumcheck.zippel",
        sizes: &[("NUM_VARS", 3), ("MAX_DEGREE_CONST", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "pst13",
        path: "examples/pst13/pst13.zippel",
        sizes: &[("N", 2)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "bccgp",
        path: "examples/bccgp/bccgp.zippel",
        sizes: &[("S", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "groth16",
        path: "examples/groth16/groth16.zippel",
        sizes: &[("M", 1), ("L", 1), ("H", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "ipa",
        path: "examples/ipa/ipa.zippel",
        sizes: &[("S", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyrax_podp",
        path: "examples/hyrax_podp/hyrax_podp.zippel",
        sizes: &[("S", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyrax_pop",
        path: "examples/hyrax_pop/hyrax_pop.zippel",
        sizes: &[],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyrax",
        path: "examples/hyrax/hyrax.zippel",
        sizes: &[("L", 2), ("M", 2)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "membership",
        path: "examples/membership/membership.zippel",
        sizes: &[("N", 2), ("M", 2), ("S", 2)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "spartan",
        path: "examples/spartan/spartan.zippel",
        sizes: &[("M", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "dory_ipa",
        path: "examples/dory_ipa/dory_ipa.zippel",
        sizes: &[("S", 2)],
        completeness: true,
        soundness: None,
    },
    // K=3 is the smallest size at which one reduce-and-fold round recurses
    // into another, not only into the final fold.
    Protocol {
        name: "dory_pcs",
        path: "examples/dory_pcs/dory_pcs.zippel",
        sizes: &[("K", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "r1cs_sigma",
        path: "examples/r1cs_sigma/r1cs_sigma.zippel",
        sizes: &[("N", 2), ("n", 1), ("m", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyperplonk_multiset",
        path: "examples/hyperplonk_multiset/hyperplonk_multiset.zippel",
        sizes: &[("S", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyperplonk_permutation",
        path: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel",
        sizes: &[("S", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyperplonk_zerocheck",
        path: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel",
        sizes: &[("S", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyperplonk_productcheck",
        path: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel",
        sizes: &[("S", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "hyperplonk_piop",
        path: "examples/hyperplonk_piop/hyperplonk_piop.zippel",
        sizes: &[("S", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "zk_kzg",
        path: "examples/zk_kzg/zk_kzg.zippel",
        sizes: &[("N", 2)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "kzh",
        path: "examples/kzh/kzh.zippel",
        sizes: &[("NX", 1), ("NY", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "dekart",
        path: "examples/dekart/dekart.zippel",
        sizes: &[("n", 3), ("b", 2), ("l_chunk", 1)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "pari",
        path: "examples/pari/pari.zippel",
        sizes: &[("M", 2), ("N", 1), ("KMN", 3)],
        completeness: true,
        soundness: None,
    },
    Protocol {
        name: "okamoto_elgamal",
        path: "examples/okamoto_elgamal/okamoto_elgamal.zippel",
        sizes: &[],
        completeness: false,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "commitment_equality",
        path: "examples/commitment_equality/commitment_equality.zippel",
        sizes: &[],
        completeness: false,
        soundness: Some(&[2]),
    },
    Protocol {
        name: "pedersen_eq",
        path: "examples/pedersen_eq/pedersen_eq.zippel",
        sizes: &[],
        completeness: false,
        soundness: Some(&[2]),
    },
];
