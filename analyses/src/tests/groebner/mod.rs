//! Test-only Groebner analysis support and regression suites.
//!
//! The legacy in-tree Buchberger and its cross-backend regression suite were
//! removed alongside the bench. Low-level GB correctness is validated by the
//! external `tests/groebner_correctness.rs` and `tests/groebner_sage.rs` suites
//! (migrated to the new API in Phase 1e).
