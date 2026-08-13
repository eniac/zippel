#![feature(box_patterns)]
#![allow(clippy::result_large_err)]

pub mod ast;
pub mod diagnostic;
pub mod id;
pub mod parser;
pub mod semantic;

pub mod typ;
pub use ast::spanned::Spanned;
