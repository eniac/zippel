//! Registered protocol examples: `zippel run <example>` or `zippel analyze <example>`.

#[path = "common/cli.rs"]
mod cli;
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

/// Register typed example descriptors and positional CLI choices.
macro_rules! examples {
    ($($name:ident),* $(,)?) => {
        fn command() -> clap::Command {
            const NAMES: &[&str] = &[$(stringify!($name)),*];
            clap::Command::new("zippel").about("Run and analyze Zippel protocol examples")
                .arg_required_else_help(true)
                .subcommand(cli::operation("run", "Prove and verify an example", NAMES, false))
                .subcommand(cli::operation("analyze", "Run static analyses", NAMES, true))
        }
        fn example_help(name: &str) -> String {
            match name {
                $(stringify!($name) => cli::example_help(&$name::spec()),)*
                _ => unreachable!("clap validates example names"),
            }
        }
        fn dispatch(name: &str, request: &common::Request) -> u8 {
            match name {
                $(stringify!($name) => common::run(name, &$name::spec(), request),)*
                _ => unreachable!("clap validates example names"),
            }
        }
    };
}

examples! {
    bccgp,
    cds,
    coin_proof,
    commitment_equality,
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
    pst13,
    r1cs_sigma,
    schnorr,
    schnorr_3round,
    spartan,
    sumcheck,
    zerocheck,
    zeromorph_kzg,
}

fn main() -> std::process::ExitCode {
    let mut command = command();
    let matches = command.clone().get_matches();
    let (operation, matches) = matches.subcommand().unwrap();
    let name = matches.get_one::<String>("example");
    if matches.get_flag("help") {
        let mut help = command
            .find_subcommand_mut(operation)
            .unwrap()
            .clone()
            .bin_name(format!("zippel {operation}"));
        if let Some(name) = name {
            help = help.after_help(example_help(name));
        }
        help.print_help().expect("write help");
        return std::process::ExitCode::SUCCESS;
    }
    let request = cli::request(matches, operation);
    std::process::ExitCode::from(dispatch(name.unwrap(), &request))
}
