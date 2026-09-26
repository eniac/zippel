//! Zippel surface language: parser, AST, and type system.
//!
//! This crate turns `.zippel` source text into a `UModule` (symbolic sizes)
//! and then a `CModule` (concrete `usize` sizes), which the `graph` crate
//! lowers into DAG IR. It owns the source-level type level `Typ<T, N>`,
//! kind-directed inference, and the diagnostics reported for both.
#![feature(deref_patterns)]
#![allow(clippy::result_large_err)]

// Allow proc-macro generated code to reference `lang::diagnostic::...`
// even when the derive is used inside the `lang` crate itself.
extern crate self as lang;

/// Untyped/typed abstract syntax: modules, declarations, expressions, spans.
pub mod ast;
pub mod diagnostic;
mod display;
/// Gensym-backed identifiers: `Tid` for size/type variables, `Vid` for values.
pub mod id;
pub mod parser;
pub mod semantic;

/// Source-level types, kinds, least-upper-bounds, unification, and inference.
pub mod typ;
pub use ast::spanned::Spanned;
