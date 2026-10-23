//! Vendored from EspressoSystems/hyperplonk `arithmetic` crate.
//! Re-exports here mirror that crate's `lib.rs`, restricted to items
//! the sum-check path actually uses.

pub mod errors;
pub mod multilinear_polynomial;
pub mod util;
pub mod virtual_polynomial;

pub use errors::ArithErrors;
pub use multilinear_polynomial::{
    evaluate_opt, fix_variables, identity_permutation, identity_permutation_mles,
    random_mle_list, random_zero_mle_list, DenseMultilinearExtension,
};
pub use util::{bit_decompose, gen_eval_point, get_batched_nv, get_index};
pub use virtual_polynomial::{
    build_eq_x_r, build_eq_x_r_vec, eq_eval, VPAuxInfo, VirtualPolynomial,
};
