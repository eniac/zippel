#![feature(box_patterns)]
#![feature(step_trait)]

pub mod id;
pub mod ast;
pub mod typ;
mod parser;

// Re-export parser initialization for external use
pub use parser::ZippelParser;
