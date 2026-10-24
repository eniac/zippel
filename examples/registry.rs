//! Example registrations shared by the normal CLI and CI harness.

#[path = "bccgp/main.rs"]
pub mod bccgp;
#[path = "cds/main.rs"]
pub mod cds;
#[path = "coin_proof/main.rs"]
pub mod coin_proof;
#[path = "cp/main.rs"]
pub mod cp;
#[path = "dekart/main.rs"]
pub mod dekart;
#[path = "dory_ipa/main.rs"]
pub mod dory_ipa;
#[path = "dory_pcs/main.rs"]
pub mod dory_pcs;
#[path = "groth16/main.rs"]
pub mod groth16;
#[path = "hadamard/main.rs"]
pub mod hadamard;
#[path = "hyperplonk_multiset/main.rs"]
pub mod hyperplonk_multiset;
#[path = "hyperplonk_permutation/main.rs"]
pub mod hyperplonk_permutation;
#[path = "hyperplonk_piop/main.rs"]
pub mod hyperplonk_piop;
#[path = "hyperplonk_productcheck/main.rs"]
pub mod hyperplonk_productcheck;
#[path = "hyperplonk_snark/main.rs"]
pub mod hyperplonk_snark;
#[path = "hyperplonk_zerocheck/main.rs"]
pub mod hyperplonk_zerocheck;
#[path = "hyrax_ipa/main.rs"]
pub mod hyrax_ipa;
#[path = "hyrax_pcs/main.rs"]
pub mod hyrax_pcs;
#[path = "hyrax_podp/main.rs"]
pub mod hyrax_podp;
#[path = "hyrax_pop/main.rs"]
pub mod hyrax_pop;
#[path = "ipa/main.rs"]
pub mod ipa;
#[path = "ipa_weighted/main.rs"]
pub mod ipa_weighted;
#[path = "kzg/main.rs"]
pub mod kzg;
#[path = "kzh/main.rs"]
pub mod kzh;
#[path = "marlin_kzg/main.rs"]
pub mod marlin_kzg;
#[path = "membership/main.rs"]
pub mod membership;
#[path = "mle_sumcheck/main.rs"]
pub mod mle_sumcheck;
#[path = "okamoto/main.rs"]
pub mod okamoto;
#[path = "okamoto_elgamal/main.rs"]
pub mod okamoto_elgamal;
#[path = "pari/main.rs"]
pub mod pari;
#[path = "pedersen_eq/main.rs"]
pub mod pedersen_eq;
#[path = "pst13/main.rs"]
pub mod pst13;
#[path = "r1cs_sigma/main.rs"]
pub mod r1cs_sigma;
#[path = "schnorr/main.rs"]
pub mod schnorr;
#[path = "schnorr_3round/main.rs"]
pub mod schnorr_3round;
#[path = "spartan/main.rs"]
pub mod spartan;
#[path = "sumcheck/main.rs"]
pub mod sumcheck;
#[path = "zerocheck/main.rs"]
pub mod zerocheck;
#[path = "zeromorph_kzg/main.rs"]
pub mod zeromorph_kzg;

macro_rules! with_examples {
    ($callback:ident) => {
        $callback! {
        bccgp,
        cds,
        coin_proof,
        cp,
        dekart,
        dory_ipa,
        dory_pcs,
        groth16,
        hadamard,
        hyperplonk_multiset,
        hyperplonk_permutation,
        hyperplonk_piop,
        hyperplonk_productcheck,
        hyperplonk_snark,
        hyperplonk_zerocheck,
        hyrax_ipa,
        hyrax_pcs,
        hyrax_podp,
        hyrax_pop,
        ipa,
        ipa_weighted,
        kzg,
        kzh,
        marlin_kzg,
        membership,
        mle_sumcheck,
        okamoto,
        okamoto_elgamal,
        pari,
        pedersen_eq,
        pst13,
        r1cs_sigma,
        schnorr,
        schnorr_3round,
        spartan,
        sumcheck,
        zerocheck,
        zeromorph_kzg,
            }
    };
}

pub(crate) use with_examples;
