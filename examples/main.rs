//! Single entry point for every Zippel protocol example.
//!
//! Each `examples/<name>/main.rs` exposes `run(&common::RunOptions)`, or
//! `run(&Args, &common::RunOptions)` with a `clap::Args` struct if it takes
//! arguments; the `examples!` list registers it as a Clap subcommand. One
//! Cargo target means one link product and one debug-info file for all
//! protocols instead of one per protocol.
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

/// Declares the `Example` subcommands and dispatches each to its module's
/// `run`. An entry written `name(args)` takes that module's `Args`.
macro_rules! examples {
    (@args $name:ident $args:ident) => { $name::Args };
    ($($name:ident $(($args:ident))?),* $(,)?) => {
        #[derive(clap::Subcommand)]
        #[command(rename_all = "snake_case")]
        #[allow(non_camel_case_types)]
        enum Example {
            $($name $((examples!(@args $name $args)))?,)*
        }

        impl Example {
            fn run(self, opts: &common::RunOptions) {
                match self {
                    $(Self::$name $(($args))? => $name::run($(&$args,)? opts),)*
                }
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
    pst13(args),
    r1cs_sigma,
    schnorr,
    schnorr_3round,
    spartan(args),
    sumcheck,
    zerocheck,
    zeromorph_kzg,
}

fn main() {
    let cli = <cli::Cli<Example> as clap::Parser>::parse();
    // Examples name their `.zippel` files relative to the repository root.
    std::env::set_current_dir(env!("CARGO_MANIFEST_DIR")).expect("repository root exists");
    if cli.no_analysis {
        println!("(static analyses skipped: --no-analysis)");
    }
    let opts = common::RunOptions {
        analyses: !cli.no_analysis,
    };
    cli.example.run(&opts);
}
