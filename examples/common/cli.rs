//! Command-line definitions for registered protocol examples.
use clap::{Arg, ArgAction, ArgMatches, Command, ValueEnum, builder::TypedValueParser};

use crate::common::{AnalysisKind, ExampleSpec, Operation, Request};

/// A selected Gröbner-basis engine.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum Backend {
    #[default]
    ArkGb,
    Singular,
}

impl From<Backend> for analyses::GbBackendKind {
    fn from(value: Backend) -> Self {
        match value {
            Backend::ArkGb => Self::ArkGb,
            Backend::Singular => Self::Singular,
        }
    }
}

/// Convert parsed CLI arguments into a harness request.
pub fn request(matches: &ArgMatches, operation: &str) -> Request {
    Request {
        sizes: matches
            .get_many::<(String, usize)>("size")
            .into_iter()
            .flatten()
            .cloned()
            .collect(),
        operation: match operation {
            "run" => Operation::Run,
            "analyze" => Operation::Analyze {
                pass: matches.get_one::<AnalysisKind>("pass").copied(),
                backend: (*matches.get_one::<Backend>("backend").unwrap()).into(),
            },
            _ => unreachable!("clap validates operation names"),
        },
    }
}

/// Details shown when help names a particular example.
pub fn example_help<C: backend::Backend>(spec: &ExampleSpec<C>) -> String {
    let mut help = String::new();
    for (label, defaults) in [
        ("Run defaults", spec.run_defaults),
        ("Analysis defaults", spec.analysis_defaults),
    ] {
        if !defaults.is_empty() {
            help.push_str(label);
            help.push_str(": ");
            help.push_str(
                &defaults
                    .iter()
                    .map(|(name, value)| format!("{name}={value}"))
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            help.push('\n');
        }
    }
    help.push_str("Analyses: ");
    help.push_str(
        &spec
            .analyses
            .iter()
            .map(|p| p.label())
            .collect::<Vec<_>>()
            .join(", "),
    );
    if spec.analyses.is_empty() {
        help.push_str("none registered");
    }
    help
}

/// Build one operation with the example as a positional choice.
pub fn operation(
    name: &'static str,
    about: &'static str,
    names: &'static [&'static str],
    analyze: bool,
) -> Command {
    let mut command = Command::new(name)
        .about(about)
        .arg_required_else_help(true)
        .disable_help_flag(true)
        .after_help(format!("Examples:\n  {}", names.join("\n  ")))
        .arg(
            Arg::new("example")
                .index(1)
                .value_name("EXAMPLE")
                .required_unless_present("help")
                .value_parser(clap::builder::PossibleValuesParser::new(
                    names.iter().copied(),
                ))
                .hide_possible_values(true)
                .help("Protocol example to use"),
        )
        .arg(
            Arg::new("help")
                .short('h')
                .long("help")
                .action(ArgAction::SetTrue)
                .help("Print help"),
        )
        .arg(
            Arg::new("size")
                .short('s')
                .long("size")
                .value_name("NAME=VALUE")
                .help("Set sizes explicitly, replacing all defaults (repeatable)")
                .action(ArgAction::Append)
                .value_parser(parse_size),
        );
    if analyze {
        command = command
            .arg(
                Arg::new("pass")
                    .index(2)
                    .value_name("ANALYSIS")
                    .value_parser(
                        clap::builder::PossibleValuesParser::new([
                            "completeness",
                            "zk",
                            "soundness",
                        ])
                        .map(|name| match name.as_str() {
                            "completeness" => AnalysisKind::Completeness,
                            "zk" => AnalysisKind::Zk,
                            "soundness" => AnalysisKind::Soundness,
                            _ => unreachable!("clap validates analysis names"),
                        }),
                    )
                    .help("Analysis to run; omitted runs all registered analyses"),
            )
            .arg(
                Arg::new("backend")
                    .long("backend")
                    .default_value("ark-gb")
                    .value_parser(clap::value_parser!(Backend))
                    .help("Gröbner-basis engine"),
            );
    }
    command
}

fn parse_size(value: &str) -> Result<(String, usize), String> {
    let (name, value) = value.split_once('=').ok_or("expected NAME=VALUE")?;
    if name.is_empty() {
        return Err("missing size name; expected NAME=VALUE".into());
    }
    let size = value
        .parse()
        .map_err(|_| format!("size `{name}` must be a non-negative integer"))?;
    Ok((name.into(), size))
}
