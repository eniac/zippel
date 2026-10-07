//! Single entry point for every Zippel protocol example.
//!
//! Each `examples/<name>/main.rs` exposes `run(&clap::ArgMatches, &common::RunOptions)`
//! and, if it takes arguments, an `args` function that defines them; `EXAMPLES`
//! registers both, and this binary uses Clap to select a protocol and parse
//! its arguments. One Cargo target means one link product and one debug-info
//! file for all protocols instead of one per protocol.
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
/// Adds an example's own arguments to its subcommand.
type Args = fn(clap::Command) -> clap::Command;

const EXAMPLES: &[(&str, Runner, Args)] = &[
    ("bccgp", bccgp::run, cli::no_args),
    ("cds", cds::run, cli::no_args),
    ("coin_proof", coin_proof::run, cli::no_args),
    (
        "commitment_equality",
        commitment_equality::run,
        cli::no_args,
    ),
    ("cp", cp::run, cli::no_args),
    ("dekart", dekart::run, cli::no_args),
    ("dory_ipa", dory_ipa::run, cli::no_args),
    ("dory_pcs", dory_pcs::run, cli::no_args),
    ("groth16", groth16::run, cli::no_args),
    ("hadamard", hadamard::run, cli::no_args),
    ("hyperplonk_piop", hyperplonk_piop::run, cli::no_args),
    (
        "hyperplonk_multiset",
        hyperplonk_multiset::run,
        cli::no_args,
    ),
    (
        "hyperplonk_permutation",
        hyperplonk_permutation::run,
        cli::no_args,
    ),
    (
        "hyperplonk_productcheck",
        hyperplonk_productcheck::run,
        cli::no_args,
    ),
    ("hyperplonk_snark", hyperplonk_snark::run, cli::no_args),
    (
        "hyperplonk_zerocheck",
        hyperplonk_zerocheck::run,
        cli::no_args,
    ),
    ("hyrax_ipa", hyrax_ipa::run, cli::no_args),
    ("hyrax_pcs", hyrax_pcs::run, cli::no_args),
    ("hyrax_podp", hyrax_podp::run, cli::no_args),
    ("hyrax_pop", hyrax_pop::run, cli::no_args),
    ("ipa", ipa::run, cli::no_args),
    ("ipa_weighted", ipa_weighted::run, cli::no_args),
    ("kzg", kzg::run, cli::no_args),
    ("kzh", kzh::run, cli::no_args),
    ("marlin_kzg", marlin_kzg::run, cli::no_args),
    ("membership", membership::run, cli::no_args),
    ("mle_sumcheck", mle_sumcheck::run, cli::no_args),
    ("okamoto", okamoto::run, cli::no_args),
    ("okamoto_elgamal", okamoto_elgamal::run, cli::no_args),
    ("pari", pari::run, cli::no_args),
    ("pedersen_eq", pedersen_eq::run, cli::no_args),
    ("pst13", pst13::run, pst13::args),
    ("r1cs_sigma", r1cs_sigma::run, cli::no_args),
    ("schnorr", schnorr::run, cli::no_args),
    ("schnorr_3round", schnorr_3round::run, cli::no_args),
    ("spartan", spartan::run, spartan::args),
    ("sumcheck", sumcheck::run, cli::no_args),
    ("zerocheck", zerocheck::run, cli::no_args),
    ("zeromorph_kzg", zeromorph_kzg::run, cli::no_args),
];

fn main() {
    let examples = EXAMPLES
        .iter()
        .map(|&(name, _, args)| args(clap::Command::new(name)));
    let matches = cli::command(examples).get_matches();
    let (name, args) = matches.subcommand().expect("Clap requires an example");
    let (_, run, _) = EXAMPLES
        .iter()
        .find(|&&(n, _, _)| n == name)
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
