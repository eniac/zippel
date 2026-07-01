//! ark-gb backend: interprets [`MonoOrder`](crate::frontend::MonoOrder) and
//! routes through the external ark-gb crate.

pub(crate) mod adapter;
mod engine;

pub use engine::ArkGb;

#[cfg(test)]
mod tests;
