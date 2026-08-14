#![feature(box_patterns)]
#![allow(clippy::result_large_err)]

// Allow proc-macro generated code to reference `lang::diagnostic::...`
// even when the derive is used inside the `lang` crate itself.
extern crate self as lang;

pub mod ast;
pub mod diagnostic;
pub mod id;
pub mod parser;
pub mod semantic;

pub mod typ;
pub use ast::spanned::Spanned;
