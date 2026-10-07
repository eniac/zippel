//! Single entry point for every Zippel protocol example.
//!
//! Each `examples/<name>/main.rs` exposes `run(&clap::ArgMatches, &common::RunOptions)`;
//! this binary uses Clap to select a protocol and parse its arguments. One Cargo
//! target means one link product and one debug-info file for all protocols
//! instead of one per protocol.
//!
//! ```text
//! cargo run --example zippel -- <name> [example args...]
//! cargo run --example zippel -- <name> --no-analysis   # prover and verifier only
//! cargo run --example zippel                 # list available examples
//! ```

#[path = "common/cli.rs"]
mod cli;
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
#[path = "dory_ipa/main.rs"]
mod dory_ipa;
#[path = "dory_pcs/main.rs"]
mod dory_pcs;
#[path = "groth16/main.rs"]
mod groth16;
#[path = "hadamard/main.rs"]
mod hadamard;
#[path = "hyperplonk_multiset/main.rs"]
mod hyperplonk_multiset;
#[path = "hyperplonk_permutation/main.rs"]
mod hyperplonk_permutation;
#[path = "hyperplonk_piop/main.rs"]
mod hyperplonk_piop;
#[path = "hyperplonk_productcheck/main.rs"]
mod hyperplonk_productcheck;
#[path = "hyperplonk_snark/main.rs"]
mod hyperplonk_snark;
#[path = "hyperplonk_zerocheck/main.rs"]
mod hyperplonk_zerocheck;
#[path = "hyrax_ipa/main.rs"]
mod hyrax_ipa;
#[path = "hyrax_pcs/main.rs"]
mod hyrax_pcs;
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
#[path = "marlin_kzg/main.rs"]
mod marlin_kzg;
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

type Runner = fn(&clap::ArgMatches, &common::RunOptions);

const EXAMPLES: &[(&str, Runner)] = &[
    ("bccgp", bccgp::run),
    ("cds", cds::run),
    ("coin_proof", coin_proof::run),
    ("commitment_equality", commitment_equality::run),
    ("cp", cp::run),
    ("dekart", dekart::run),
    ("dory_ipa", dory_ipa::run),
    ("dory_pcs", dory_pcs::run),
    ("groth16", groth16::run),
    ("hadamard", hadamard::run),
    ("hyperplonk_piop", hyperplonk_piop::run),
    ("hyperplonk_multiset", hyperplonk_multiset::run),
    ("hyperplonk_permutation", hyperplonk_permutation::run),
    ("hyperplonk_productcheck", hyperplonk_productcheck::run),
    ("hyperplonk_snark", hyperplonk_snark::run),
    ("hyperplonk_zerocheck", hyperplonk_zerocheck::run),
    ("hyrax_ipa", hyrax_ipa::run),
    ("hyrax_pcs", hyrax_pcs::run),
    ("hyrax_podp", hyrax_podp::run),
    ("hyrax_pop", hyrax_pop::run),
    ("ipa", ipa::run),
    ("ipa_weighted", ipa_weighted::run),
    ("kzg", kzg::run),
    ("kzh", kzh::run),
    ("marlin_kzg", marlin_kzg::run),
    ("membership", membership::run),
    ("mle_sumcheck", mle_sumcheck::run),
    ("okamoto", okamoto::run),
    ("okamoto_elgamal", okamoto_elgamal::run),
    ("pari", pari::run),
    ("pedersen_eq", pedersen_eq::run),
    ("pst13", pst13::run),
    ("r1cs_sigma", r1cs_sigma::run),
    ("schnorr", schnorr::run),
    ("schnorr_3round", schnorr_3round::run),
    ("spartan", spartan::run),
    ("sumcheck", sumcheck::run),
    ("zerocheck", zerocheck::run),
    ("zeromorph_kzg", zeromorph_kzg::run),
];

fn main() {
    let matches = cli::command(EXAMPLES.iter().map(|&(name, _)| name)).get_matches();
    let (name, args) = matches.subcommand().expect("Clap requires an example");
    let (_, run) = EXAMPLES
        .iter()
        .find(|&&(n, _)| n == name)
        .expect("Clap only accepts registered examples");
    let no_analysis = matches.get_flag("no_analysis");
    if no_analysis {
        println!("(static analyses skipped: --no-analysis)");
    }
    let opts = common::RunOptions {
        analyses: !no_analysis,
    };
    run(args, &opts);
}
