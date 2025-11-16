#![feature(associated_type_defaults)]
#![feature(trait_alias)]
#![feature(box_patterns)]
pub mod graph;

pub use graph::MutexGraph;

#[cfg(test)]
mod tests;


