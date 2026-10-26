//! Registered protocol examples: `zippel run <example>`, `zippel analyze <example>`
//! or `zippel list`.

#[path = "common/cli.rs"]
mod cli;
mod common;

mod registry;

/// Register typed example descriptors and positional CLI choices.
macro_rules! examples {
    ($($name:ident),* $(,)?) => {
        const NAMES: &[&str] = &[$(stringify!($name)),*];
        fn command() -> clap::Command {
            clap::Command::new("zippel").about("Run and analyze Zippel protocol examples")
                .arg_required_else_help(true)
                .subcommand(cli::operation("run", "Prove and verify an example", NAMES, false))
                .subcommand(cli::operation("analyze", "Run static analyses", NAMES, true))
                .subcommand(clap::Command::new("list").about("Print example names, one per line"))
        }
        fn example_help(name: &str) -> String {
            match name {
                $(stringify!($name) => cli::example_help(&registry::$name::spec()),)*
                _ => unreachable!("clap validates example names"),
            }
        }
        fn dispatch(name: &str, request: &common::Request) -> u8 {
            match name {
                $(stringify!($name) => common::run(name, &registry::$name::spec(), request),)*
                _ => unreachable!("clap validates example names"),
            }
        }
    };
}

registry::with_examples!(examples);

fn main() -> std::process::ExitCode {
    let mut command = command();
    let matches = command.clone().get_matches();
    let (operation, matches) = matches.subcommand().unwrap();
    if operation == "list" {
        for name in NAMES {
            println!("{name}");
        }
        return std::process::ExitCode::SUCCESS;
    }
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
