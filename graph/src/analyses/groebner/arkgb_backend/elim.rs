//! Port of `isolate_elimination_vars` over [`AdapterPoly`].
//!
//! Under the GrevLex-only v1 backend, "elimination variables" are not
//! distinguished by the monomial order itself; they're handled at this
//! higher level by isolating polynomials whose support intersects the
//! caller-provided elimination set.
//!
//! See the original implementation in `analyses/groebner/sparsepoly.rs`
//! for the reference semantics.

use crate::pref::PRef;
use ark_ff::Field;
use share::Set;

use super::poly::AdapterPoly;

/// Partition `polys` into `(eliminated, retained)` based on whether each
/// polynomial's support intersects `elim_vars`. Mirrors the behaviour of
/// the in-tree `isolate_elimination_vars`.
pub fn isolate_elimination_vars<F: Field + Copy + Send + Sync>(
    _polys: Vec<AdapterPoly<F>>,
    _elim_vars: &Set<PRef>,
) -> (Vec<AdapterPoly<F>>, Vec<AdapterPoly<F>>) {
    unimplemented!("isolate_elimination_vars — implemented in P2")
}
