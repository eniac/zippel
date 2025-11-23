#![feature(box_patterns)]
#![feature(step_trait)]

/// Initialize pest parser settings for better error messages.
/// This enables more comprehensive error messages from the parser.
pub fn init_parser() {
    pest::set_error_detail(true);
}

pub mod id;
pub mod ast;
pub mod typ;
mod parser;
