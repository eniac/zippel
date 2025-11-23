mod error;
pub use error::InputError;

use pest_derive::Parser;

/// Pest parser for zippel
#[derive(Parser)]
#[grammar = "parser/zippel.pest"] // relative to src
pub struct ZippelParser;

