//! Vendored from EspressoSystems/hyperplonk `arithmetic` crate.
//! Re-exports here mirror that crate's `lib.rs`, restricted to items
//! the sum-check path actually uses.

pub mod errors;
pub mod multilinear_polynomial;
pub mod util;
pub mod virtual_polynomial;

pub use errors::ArithErrors;
pub use multilinear_polynomial::{
    fix_variables, random_mle_list, random_zero_mle_list, DenseMultilinearExtension,
};
pub use util::{bit_decompose, get_batched_nv, get_index};
pub use virtual_polynomial::{VPAuxInfo, VirtualPolynomial};
