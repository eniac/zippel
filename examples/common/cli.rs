//! Command-line definitions shared by every protocol example.

/// The harness CLI: shared options plus one subcommand per example in `E`.
#[derive(clap::Parser, Debug)]
#[command(
    name = "zippel",
    about = "Run a Zippel protocol example",
    arg_required_else_help = true,
    disable_help_subcommand = true,
    args_override_self = true
)]
pub struct Cli<E: clap::Subcommand> {
    /// Run only the prover and verifier, skipping static analyses
    #[arg(long, global = true)]
    pub no_analysis: bool,
    /// The example to run, with its own arguments.
    #[command(subcommand)]
    pub example: E,
}
