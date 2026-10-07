//! Regression tests for the protocol-agnostic example harness command line.

#[path = "../examples/common/cli.rs"]
mod cli;

use clap::{Parser, error::ErrorKind};

/// Two stand-in examples: one without arguments of its own, and one with a
/// positional value, an option, and a flag.
#[derive(clap::Subcommand, Debug, PartialEq, Eq)]
#[command(rename_all = "snake_case")]
enum Example {
    Plain,
    WithArgs(WithArgs),
}

#[derive(clap::Args, Debug, PartialEq, Eq)]
struct WithArgs {
    size: Option<usize>,
    #[arg(long, value_name = "PATH")]
    path: Option<String>,
    #[arg(long)]
    flag: bool,
}

type Cli = cli::Cli<Example>;

fn with_args(size: Option<usize>, path: &str, flag: bool) -> Example {
    Example::WithArgs(WithArgs {
        size,
        path: Some(path.into()),
        flag,
    })
}

#[test]
fn harness_flag_works_anywhere_around_example_arguments() {
    for args in [
        vec!["zippel", "--no-analysis", "with_args", "3", "--path", "p"],
        vec!["zippel", "with_args", "--no-analysis", "3", "--path", "p"],
        vec!["zippel", "with_args", "3", "--no-analysis", "--path", "p"],
        vec!["zippel", "with_args", "3", "--path", "p", "--no-analysis"],
        vec![
            "zippel",
            "--no-analysis",
            "with_args",
            "3",
            "--path",
            "p",
            "--no-analysis",
        ],
    ] {
        let cli = Cli::try_parse_from(args).unwrap();
        assert!(cli.no_analysis);
        assert_eq!(cli.example, with_args(Some(3), "p", false));
    }
}

#[test]
fn analyses_run_by_default() {
    let cli = Cli::try_parse_from(["zippel", "plain"]).unwrap();
    assert!(!cli.no_analysis);
    assert_eq!(cli.example, Example::Plain);
}

#[test]
fn a_value_that_looks_like_the_harness_flag_is_preserved() {
    let cli = Cli::try_parse_from(["zippel", "with_args", "--path=--no-analysis"]).unwrap();
    assert!(!cli.no_analysis);
    assert_eq!(cli.example, with_args(None, "--no-analysis", false));
}

#[test]
fn repeated_flags_and_options_override_earlier_ones() {
    let cli = Cli::try_parse_from([
        "zippel",
        "with_args",
        "--no-analysis",
        "--no-analysis",
        "--flag",
        "--flag",
        "--path",
        "first",
        "--path",
        "last",
    ])
    .unwrap();
    assert!(cli.no_analysis);
    assert_eq!(cli.example, with_args(None, "last", true));
}

#[test]
fn help_lists_examples_and_the_harness_flag() {
    for (args, expected) in [
        (vec!["zippel", "--help"], "with_args"),
        (vec!["zippel", "plain", "--help"], "Usage: zippel plain"),
        (vec!["zippel", "with_args", "--help"], "--path <PATH>"),
    ] {
        let error = Cli::try_parse_from(args).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::DisplayHelp);
        let help = error.to_string();
        assert!(help.contains(expected));
        assert!(help.contains("--no-analysis"));
    }
}

#[test]
fn missing_or_unknown_examples_and_unexpected_arguments_are_errors() {
    for args in [
        vec!["zippel"],
        vec!["zippel", "--no-analysis"],
        vec!["zippel", "unknown"],
        vec!["zippel", "plain", "--no-analyis"],
        vec!["zippel", "plain", "extra"],
        vec!["zippel", "with_args", "invalid"],
        vec!["zippel", "with_args", "--path"],
    ] {
        let error = Cli::try_parse_from(args).unwrap_err();
        assert_eq!(error.exit_code(), 2);
    }
}
