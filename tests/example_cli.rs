//! Regression tests for the protocol-agnostic example harness command line.

#[path = "../examples/common/cli.rs"]
mod cli;

use clap::{Arg, ArgAction, Command, error::ErrorKind};

/// The harness with two stand-in examples: one without arguments of its own,
/// and one with a positional value, an option, and a flag.
fn command() -> Command {
    let plain = cli::no_args(Command::new("plain"));
    let with_args = Command::new("with_args")
        .arg(Arg::new("size").value_parser(clap::value_parser!(usize)))
        .arg(Arg::new("path").long("path").value_name("PATH"))
        .arg(Arg::new("flag").long("flag").action(ArgAction::SetTrue));
    cli::command([plain, with_args])
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
        let matches = command().try_get_matches_from(args).unwrap();
        assert!(matches.get_flag("no_analysis"));
        let (name, example) = matches.subcommand().unwrap();
        assert_eq!(name, "with_args");
        assert_eq!(example.get_one::<usize>("size"), Some(&3));
        assert_eq!(example.get_one::<String>("path").unwrap(), "p");
    }
}

#[test]
fn analyses_run_by_default() {
    let matches = command().try_get_matches_from(["zippel", "plain"]).unwrap();
    assert!(!matches.get_flag("no_analysis"));
    assert_eq!(matches.subcommand_name(), Some("plain"));
}

#[test]
fn a_value_that_looks_like_the_harness_flag_is_preserved() {
    let matches = command()
        .try_get_matches_from(["zippel", "with_args", "--path=--no-analysis"])
        .unwrap();
    assert!(!matches.get_flag("no_analysis"));
    assert_eq!(
        matches
            .subcommand()
            .unwrap()
            .1
            .get_one::<String>("path")
            .unwrap(),
        "--no-analysis"
    );
}

#[test]
fn repeated_flags_and_options_override_earlier_ones() {
    let matches = command()
        .try_get_matches_from([
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
    assert!(matches.get_flag("no_analysis"));
    let example = matches.subcommand().unwrap().1;
    assert!(example.get_flag("flag"));
    assert_eq!(example.get_one::<String>("path").unwrap(), "last");
}

#[test]
fn help_lists_examples_and_the_harness_flag() {
    for (args, expected) in [
        (vec!["zippel", "--help"], "with_args"),
        (vec!["zippel", "plain", "--help"], "Usage: zippel plain"),
        (vec!["zippel", "with_args", "--help"], "--path <PATH>"),
    ] {
        let error = command().try_get_matches_from(args).unwrap_err();
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
        let error = command().try_get_matches_from(args).unwrap_err();
        assert_eq!(error.exit_code(), 2);
    }
}
