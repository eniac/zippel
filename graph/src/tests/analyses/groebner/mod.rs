//! Test-only Groebner analysis support and regression suites.

pub mod buchberger;
pub(crate) mod legacy;
pub mod regression;

#[path = "../../../../../benches/groebner_shared.rs"]
pub(crate) mod shared;
