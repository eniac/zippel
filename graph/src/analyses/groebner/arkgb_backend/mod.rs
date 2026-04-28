//! ark-gb backend for Groebner-basis computation.
//!
//! This module is gated behind the `arkgb_backend` cargo feature. When enabled,
//! `GroebnerBasis<F, T>` and `SparsePolynomial<F, T>` are routed through
//! adapter types that delegate the heavy lifting (Buchberger, S-polynomials,
//! reduction) to the upstream `ark-gb` crate.
//!
//! ## Layout
//!
//! - [`ring`] — `VarRing<F>`: PRef↔u32 variable interner plus a lazily-built
//!   `Arc<ark_gb::ring::Ring<F, W>>`.
//! - [`poly`] — `AdapterPoly<F>`: dual-form polynomial. Construction-phase
//!   arithmetic accumulates into a lazy `Vec<(F, Vec<(u32, u32)>)>` exponent
//!   list; the moment the basis algorithm needs an ark-gb `Poly`, the term
//!   list is materialised into `ark_gb::Poly<F, GrevLexTerm<W>, W>`.
//! - [`monomial`] — `AdapterMonomial<F>`: implements zippel's `Monomial` trait
//!   and exposes `vars()` / `powers()` by mapping back through the `VarRing`.
//! - [`basis`] — `AdapterGroebnerBasis<F>`: Buchberger driver; just a thin
//!   wrapper around `ark_gb::compute_gb`.
//! - [`elim`] — Port of `isolate_elimination_vars` over `AdapterPoly`.
//!
//! ## Const-generic W
//!
//! The default packing width is `W = 8` (cap = 63 variables). Bumping to
//! `W = 16` gives 127 variables at the cost of doubling per-monomial bytes.
//! See [`W`].

/// Default ark-gb packing width used by this backend.
///
/// `W = 8` allows up to 63 variables in a single ring, which comfortably
/// covers all current Zippel examples. If a future workload exceeds that,
/// bump to `W = 16` (cap = 127).
pub const W: usize = 8;

pub mod basis;
pub mod elim;
pub mod monomial;
pub mod poly;
pub mod ring;

pub use basis::AdapterGroebnerBasis;
pub use monomial::AdapterMonomial;
pub use poly::AdapterPoly;
pub use ring::VarRing;
