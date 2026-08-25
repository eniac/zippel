//! Op encoder infrastructure: `EncodeCtx` and per-op encoder modules.
//!
//! Each op encoder is a free function taking `&mut EncodeCtx`. The context
//! provides mutable access to the `IdealBuilder` (for sentinel/witness
//! allocation and recursive `add_op` dispatch) and the ideal being built.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};

use crate::Var;
use crate::frontend::Polynomial;

// Barrel re-exports for child modules. Children use `super::X` instead of
// `super::super::X`, and test modules use `super::super::X` instead of
// `crate::X`.
pub(crate) use super::Ideal;
pub(crate) use super::IdealBuilder;
pub(crate) use super::PolySource;
pub(crate) use super::combinatorics::{dft_row, hypercube, lagrange_basis, multi_indices};

/// Context passed to every op encoder. Provides access to the
/// `IdealBuilder` (for sentinel allocation and recursive `add_op`
/// dispatch) and the ideal being built.
pub struct EncodeCtx<'a, C: ArkConfig> {
    pub builder: &'a mut IdealBuilder<C>,
    pub ideal: &'a mut Ideal<C>,
}

impl<'a, C: ArkConfig + HasOpFactory> EncodeCtx<'a, C> {
    /// Allocate a sentinel variable with `name` and `typ`, registering it
    /// in the ideal's var_order.
    pub fn sentinel_var(&mut self, name: &str, typ: ATyp) -> Var {
        self.builder.sentinel_var(name, typ, self.ideal)
    }
}

/// Link the user's Var `var` to a witness Var `wit` slot by slot.
/// Emits `var(var[j]) − var(wit[j]) = 0` for every slot, and
/// registers `pl[var[j]] = var(wit[j])`.
///
/// The type checker computes exact degree bounds for quotient
/// (`m - m'`) and remainder (`m' - 1`), so the witness and target
/// must have the same number of physical slots. A mismatch indicates
/// a bug in either the type checker or the caller.
pub fn link_to_witness<C: ArkConfig>(ideal: &mut Ideal<C>, var: &Var, wit: &Var) {
    let var_slots = var.slots();
    let wit_slots = wit.slots();
    assert_eq!(
        var_slots.len(),
        wit_slots.len(),
        "link_to_witness: slot count mismatch — var {} has {} slots, wit {} has {}",
        var.verbose(),
        var_slots.len(),
        wit.verbose(),
        wit_slots.len(),
    );
    for (pf, wf) in var_slots.into_iter().zip(wit_slots) {
        let wvar = Polynomial::var(&wf);
        ideal.pl.insert(&pf, &wvar);
        ideal.generating_set.push(&wvar - &Polynomial::var(&pf));
    }
}

/// Link each slot of `var` to the corresponding polynomial in `polys`.
/// Registers `pl[var[j]] = polys[j]` and emits `polys[j] − var(var[j]) = 0`.
///
/// Asserts that `var` has exactly `polys.len()` physical slots.
pub fn link_to_polys<C: ArkConfig>(ideal: &mut Ideal<C>, var: &Var, polys: Vec<Polynomial<C::F>>) {
    let var_slots = var.slots();
    assert_eq!(
        var_slots.len(),
        polys.len(),
        "link_to_polys: slot count mismatch — var {} has {} slots, polys has {}",
        var.verbose(),
        var_slots.len(),
        polys.len(),
    );
    for (pf, p) in var_slots.into_iter().zip(polys) {
        ideal.pl.insert(&pf, &p);
        ideal.generating_set.push(p - Polynomial::var(&pf));
    }
}

pub mod addsub;
pub mod bool;
pub mod check;
pub mod concat;
pub mod div;
pub mod dot;
pub mod eval;
pub mod fft;
pub mod interpolate;
pub mod map;
pub mod mul;
pub mod pair;
pub mod pow;
pub mod ram;
pub mod record;
pub mod reduce;
pub mod test_helpers;
pub mod value;

/// Panic with a standard message when an operation has no polynomial-ideal
/// treatment. `context` is a short kebab-case string identifying the code
/// path (e.g. `"concat-non-vector"`, `"dynamic-pow"`).
pub fn uncovered_op(context: &str, target: &Var) -> ! {
    panic!(
        "ideal: operation has no polynomial-ideal treatment at {} for {}",
        context,
        target.verbose()
    )
}
