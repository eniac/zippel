#![feature(box_patterns)]
#![feature(step_trait)]

use std::sync::Once;

static INIT_PARSER: Once = Once::new();

/// Initialize pest parser settings for better error messages.
/// This enables more comprehensive error messages from the parser.
/// Uses Once to ensure thread-safe, one-time initialization.
pub fn init_parser() {
    INIT_PARSER.call_once(|| {
        pest::set_error_detail(true);
    });
}

pub mod id;
pub mod ast;
pub mod typ;
mod parser;
