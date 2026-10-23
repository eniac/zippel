//! Polynomials: concrete encodings and the virtual sums of products sumcheck rounds use.

/// Concrete polynomial encodings (dense/sparse univariate, multilinear,
/// sparse multivariate) and the arithmetic defined over them.
pub mod variant;
/// Sum-of-products polynomial representation used by sumcheck-style protocols.
pub mod virtual_polynomial;
