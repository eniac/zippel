//! Command-line definitions shared by every protocol example.

use clap::{Arg, ArgAction, Command};

/// Build the harness CLI with one subcommand per example.
pub fn command(examples: impl IntoIterator<Item = Command>) -> Command {
    Command::new("zippel")
        .about("Run a Zippel protocol example")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .disable_help_subcommand(true)
        .args_override_self(true)
        .arg(
            Arg::new("no_analysis")
                .long("no-analysis")
                .global(true)
                .action(ArgAction::SetTrue)
                .help("Run only the prover and verifier, skipping static analyses"),
        )
        .subcommands(examples)
}

/// Argument definitions for an example that takes no arguments of its own.
pub const fn no_args(command: Command) -> Command {
    command
}
