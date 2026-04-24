#![feature(box_patterns)]

use lazy_static::lazy_static;

lazy_static! {
    /// Initialize pest parser settings for better error messages.
    /// This enables more comprehensive error messages from the parser.
    static ref INIT_PARSER: () = {
        pest::set_error_detail(true);
    };
}

/// Initialize pest parser settings for better error messages.
/// This ensures the lazy_static initialization is triggered.
pub fn init_parser() {
    lazy_static::initialize(&INIT_PARSER);
}

pub mod ast;
pub mod id;
mod parser;
pub mod typ;
