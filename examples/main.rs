//! Single entry point for every Zippel protocol example.
//!
//! Each `examples/<name>/main.rs` exposes `pub fn run(args: &[String])`; this
//! binary dispatches on `argv[1]` and forwards `argv[2..]` to it. One Cargo
//! target means one link product and one debug-info file for all protocols
//! instead of one per protocol.
//!
//! ```text
//! cargo run --example zippel -- <name> [example args...]
//! cargo run --example zippel                 # list available examples
//! ```

#[path = "common/analysis.rs"]
mod common;

#[path = "bccgp/main.rs"]
mod bccgp;
#[path = "cds/main.rs"]
mod cds;
#[path = "coin_proof/main.rs"]
mod coin_proof;
#[path = "commitment_equality/main.rs"]
mod commitment_equality;
#[path = "cp/main.rs"]
mod cp;
#[path = "dekart/main.rs"]
mod dekart;
#[path = "dory/main.rs"]
mod dory;
#[path = "groth16/main.rs"]
mod groth16;
#[path = "hadamard/main.rs"]
mod hadamard;
#[path = "hyperplonk/main.rs"]
mod hyperplonk;
#[path = "hyperplonk_multiset/main.rs"]
mod hyperplonk_multiset;
#[path = "hyperplonk_permutation/main.rs"]
mod hyperplonk_permutation;
#[path = "hyperplonk_productcheck/main.rs"]
mod hyperplonk_productcheck;
#[path = "hyperplonk_zerocheck/main.rs"]
mod hyperplonk_zerocheck;
#[path = "hyrax/main.rs"]
mod hyrax;
#[path = "hyrax_ipa/main.rs"]
mod hyrax_ipa;
#[path = "hyrax_podp/main.rs"]
mod hyrax_podp;
#[path = "hyrax_pop/main.rs"]
mod hyrax_pop;
#[path = "ipa/main.rs"]
mod ipa;
#[path = "ipa_weighted/main.rs"]
mod ipa_weighted;
#[path = "kzg/main.rs"]
mod kzg;
#[path = "kzh/main.rs"]
mod kzh;
#[path = "membership/main.rs"]
mod membership;
#[path = "mle_sumcheck/main.rs"]
mod mle_sumcheck;
#[path = "okamoto/main.rs"]
mod okamoto;
#[path = "okamoto_elgamal/main.rs"]
mod okamoto_elgamal;
#[path = "pari/main.rs"]
mod pari;
#[path = "pedersen_eq/main.rs"]
mod pedersen_eq;
#[path = "pst13/main.rs"]
mod pst13;
#[path = "r1cs_sigma/main.rs"]
mod r1cs_sigma;
#[path = "sc_test_m3/main.rs"]
mod sc_test_m3;
#[path = "schnorr/main.rs"]
mod schnorr;
#[path = "schnorr_3round/main.rs"]
mod schnorr_3round;
#[path = "spartan/main.rs"]
mod spartan;
#[path = "sumcheck/main.rs"]
mod sumcheck;
#[path = "zerocheck/main.rs"]
mod zerocheck;
#[path = "zeromorph_kzg/main.rs"]
mod zeromorph_kzg;
#[path = "zk_kzg/main.rs"]
mod zk_kzg;

type Runner = fn(&[String]);

const EXAMPLES: &[(&str, Runner)] = &[
    ("bccgp", bccgp::run),
    ("cds", cds::run),
    ("coin_proof", coin_proof::run),
    ("commitment_equality", commitment_equality::run),
    ("cp", cp::run),
    ("dekart", dekart::run),
    ("dory", dory::run),
    ("groth16", groth16::run),
    ("hadamard", hadamard::run),
    ("hyperplonk", hyperplonk::run),
    ("hyperplonk_multiset", hyperplonk_multiset::run),
    ("hyperplonk_permutation", hyperplonk_permutation::run),
    ("hyperplonk_productcheck", hyperplonk_productcheck::run),
    ("hyperplonk_zerocheck", hyperplonk_zerocheck::run),
    ("hyrax", hyrax::run),
    ("hyrax_ipa", hyrax_ipa::run),
    ("hyrax_podp", hyrax_podp::run),
    ("hyrax_pop", hyrax_pop::run),
    ("ipa", ipa::run),
    ("ipa_weighted", ipa_weighted::run),
    ("kzg", kzg::run),
    ("kzh", kzh::run),
    ("membership", membership::run),
    ("mle_sumcheck", mle_sumcheck::run),
    ("okamoto", okamoto::run),
    ("okamoto_elgamal", okamoto_elgamal::run),
    ("pari", pari::run),
    ("pedersen_eq", pedersen_eq::run),
    ("pst13", pst13::run),
    ("r1cs_sigma", r1cs_sigma::run),
    ("sc_test_m3", sc_test_m3::run),
    ("schnorr", schnorr::run),
    ("schnorr_3round", schnorr_3round::run),
    ("spartan", spartan::run),
    ("sumcheck", sumcheck::run),
    ("zerocheck", zerocheck::run),
    ("zeromorph_kzg", zeromorph_kzg::run),
    ("zk_kzg", zk_kzg::run),
];

fn usage() {
    eprintln!("usage: cargo run --example zippel -- <name> [example args...]");
    eprintln!("available examples:");
    for (name, _) in EXAMPLES {
        eprintln!("  {name}");
    }
}

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    let Some(name) = argv.get(1) else {
        usage();
        std::process::exit(2);
    };
    let Some(&(_, run)) = EXAMPLES.iter().find(|&&(n, _)| n == name.as_str()) else {
        eprintln!("unknown example: {name}");
        usage();
        std::process::exit(2);
    };
    run(&argv[2..]);
}
