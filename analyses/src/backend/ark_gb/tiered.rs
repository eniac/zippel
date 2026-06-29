use crate::backend::ark_gb::adapter::get_local_rank;
use crate::backend::ark_gb::sparsepoly::SparsePolynomial;
use ark_ff::Field;
use core::cmp::Ordering;
use core::ops::{Div, Mul, MulAssign};
use graph::PRef;
use share::Ctx;
use std::fmt;
use std::fmt::Debug;

use crate::backend::ark_gb::monomial::{MonoTerm, Monomial as ZipMonomial};

/// Strategy that assigns each `PRef` to a tier in a tiered elimination order.
///
/// Tier 0 is compared lexicographically (variables with smaller [`lex_rank`]
/// are "larger", i.e. become leading terms first).  Tiers ≥ 1 are compared
/// via degree-reverse-lexicographic (grevlex) order.  Variables that return
/// `None` from [`tier`] are excluded from the computation entirely.
///
/// This trait is the zippel-side counterpart to the ark-gb wrapper
/// [`ZippelTieredElimMono`](crate::backend::ark_gb::adapter::ZippelTieredElimMono),
/// which encodes the same tiered order into ark-gb's packed-byte key format.
pub trait TieredElimStrategy: Sized + Send + Sync {
    /// Which tier the variable belongs to, or `None` to exclude it.
    fn tier(v: &PRef) -> Option<usize>;

    /// Lexicographic rank *within* tier 0.  Larger rank → variable is
    /// compared first in the lex order (higher elimination priority).
    /// Defaults to [`get_local_rank`], which reflects the order in which
    /// locals were bound.
    fn lex_rank(v: &PRef) -> usize {
        get_local_rank(v).unwrap()
    }
}

/// Zippel-side monomial type parametric on a [`TieredElimStrategy`].
///
/// `TieredElimMono<E>` wraps a [`MonoTerm`] (a variable-exponent map) and
/// delegates all arithmetic to it.  The only thing it adds is an [`Ord`]
/// implementation that realises the tiered elimination order defined by `E`,
/// and a [`ZipMonomial::compute_reduced_gb`] entry point that routes through
/// ark-gb's tiered backend.
///
/// # Ordering convention
///
/// This type is used inside zippel's `BTreeMap`-backed `SparsePolynomial`,
/// where **`Less` = leading** (the leading term sorts first / is smallest).
/// The ark-gb wrapper `ZippelTieredElimMono` uses the **opposite**
/// convention (`Greater` = leading) because ark-gb's `Poly` and max-heap
/// expect it; `cmp_key` is inverted accordingly.
pub struct TieredElimMono<E: TieredElimStrategy>(MonoTerm, std::marker::PhantomData<E>);

impl<E: TieredElimStrategy> Clone for TieredElimMono<E> {
    fn clone(&self) -> Self {
        TieredElimMono(self.0.clone(), std::marker::PhantomData)
    }
}

impl<E: TieredElimStrategy> PartialEq for TieredElimMono<E> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<E: TieredElimStrategy> Eq for TieredElimMono<E> {}

impl<E: TieredElimStrategy> Debug for TieredElimMono<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("TieredElimMono").field(&self.0).finish()
    }
}

impl<E: TieredElimStrategy> From<MonoTerm> for TieredElimMono<E> {
    fn from(t: MonoTerm) -> Self {
        TieredElimMono(t, std::marker::PhantomData)
    }
}

impl<E: TieredElimStrategy> TieredElimMono<E> {
    /// Build a monomial from a `PRef → exponent` map.
    pub fn new(vars: Ctx<PRef, usize>) -> Self {
        TieredElimMono(MonoTerm(vars), std::marker::PhantomData)
    }

    /// Iterate over `(variable, exponent)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&PRef, &usize)> {
        self.0.iter()
    }

    /// Access the underlying [`MonoTerm`].
    pub(crate) fn as_mono_term(&self) -> &MonoTerm {
        &self.0
    }
}

impl<E: TieredElimStrategy> Default for TieredElimMono<E> {
    fn default() -> Self {
        TieredElimMono(MonoTerm(Ctx::new()), std::marker::PhantomData)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl<E: TieredElimStrategy> MulAssign for TieredElimMono<E> {
    fn mul_assign(&mut self, other: Self) {
        for (var, power) in other.0.iter() {
            *self.0.0.entry(var.clone()).or_insert(0) += power;
        }
    }
}

impl<E: TieredElimStrategy> Mul for TieredElimMono<E> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<'a, E: TieredElimStrategy> Mul for &'a TieredElimMono<E> {
    type Output = TieredElimMono<E>;

    fn mul(self, other: &'a TieredElimMono<E>) -> TieredElimMono<E> {
        self.clone() * other.clone()
    }
}

impl<E: TieredElimStrategy> fmt::Display for TieredElimMono<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<E: TieredElimStrategy> Div for TieredElimMono<E> {
    type Output = Option<Self>;

    fn div(self, other: Self) -> Option<Self> {
        self.0.div(other.0).map(TieredElimMono::from)
    }
}

impl<'a, E: TieredElimStrategy> Div for &'a TieredElimMono<E> {
    type Output = Option<TieredElimMono<E>>;

    fn div(self, other: &'a TieredElimMono<E>) -> Option<TieredElimMono<E>> {
        self.clone() / other.clone()
    }
}

impl<E: TieredElimStrategy> From<Vec<(PRef, usize)>> for TieredElimMono<E> {
    fn from(vars: Vec<(PRef, usize)>) -> Self {
        TieredElimMono::new(vars.into_iter().collect())
    }
}

impl<E: TieredElimStrategy> ZipMonomial for TieredElimMono<E> {
    fn vars(&self) -> Vec<PRef> {
        self.0.vars()
    }

    fn powers(&self) -> Vec<usize> {
        self.0.powers()
    }

    fn is_constant(&self) -> bool {
        self.0.is_constant()
    }

    fn is_divided(&self, other: &Self) -> bool {
        self.0.is_divided(&other.0)
    }

    fn lcm(&self, other: &Self) -> Self {
        TieredElimMono(self.0.lcm(&other.0), std::marker::PhantomData)
    }

    fn compute_reduced_gb<F: Field, const W: usize>(
        num_vars: usize,
        input: Vec<SparsePolynomial<F, Self>>,
    ) -> Vec<SparsePolynomial<F, Self>>
    where
        Self: Sized,
    {
        use crate::backend::ark_gb::adapter::compute_reduced_gb_with_tiered_elim;
        compute_reduced_gb_with_tiered_elim::<F, Self, E, W>(num_vars, input)
    }
}

/// Tiered elimination order: tiers are compared in ascending order;
/// within tier 0 the comparison is lexicographic (smaller `lex_rank` =
/// leading); within tiers ≥ 1 the comparison is grevlex (higher degree =
/// trailing; right-to-left tiebreak with larger exponent = leading).
///
/// Returns [`Ordering::Less`] when `self` is the *leading* monomial,
/// matching zippel's `BTreeMap` convention where the smallest element is
/// the leading term.
impl<E: TieredElimStrategy> Ord for TieredElimMono<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        let all_vars: Vec<PRef> = {
            let mut vs: Vec<PRef> = self
                .0
                .iter()
                .chain(other.0.iter())
                .map(|(v, _)| v.clone())
                .collect();
            vs.sort();
            vs.dedup();
            vs
        };

        let mut tier_map: std::collections::BTreeMap<usize, Vec<PRef>> =
            std::collections::BTreeMap::new();
        for v in &all_vars {
            if let Some(t) = E::tier(v) {
                tier_map.entry(t).or_default().push(v.clone());
            }
        }

        let mut non_empty_tiers: Vec<(usize, Vec<PRef>)> = tier_map
            .into_iter()
            .filter(|(_, g)| !g.is_empty())
            .collect();

        if let Some((0, tier0_vars)) = non_empty_tiers.first_mut() {
            tier0_vars.sort_by(|a, b| {
                let ra = E::lex_rank(a);
                let rb = E::lex_rank(b);
                rb.cmp(&ra).then_with(|| a.cmp(b))
            });
        }

        for tier in non_empty_tiers.iter_mut().skip(1) {
            if tier.0 > 0 {
                tier.1.sort();
            }
        }

        for (raw_tier, tier_vars) in &non_empty_tiers {
            let is_tier0 = *raw_tier == 0;

            if is_tier0 {
                for v in tier_vars {
                    let e_self: usize = self
                        .0
                        .iter()
                        .find(|(vv, _)| *vv == v)
                        .map(|(_, &p)| p)
                        .unwrap_or(0);
                    let e_other: usize = other
                        .0
                        .iter()
                        .find(|(vv, _)| *vv == v)
                        .map(|(_, &p)| p)
                        .unwrap_or(0);
                    match e_self.cmp(&e_other) {
                        Ordering::Equal => continue,
                        Ordering::Greater => return Ordering::Less,
                        Ordering::Less => return Ordering::Greater,
                    }
                }
            } else {
                let self_tier: MonoTerm = MonoTerm(
                    tier_vars
                        .iter()
                        .filter_map(|v| {
                            self.0
                                .iter()
                                .find(|(vv, _)| *vv == v)
                                .map(|(vv, &p)| (vv.clone(), p))
                        })
                        .collect(),
                );
                let other_tier: MonoTerm = MonoTerm(
                    tier_vars
                        .iter()
                        .filter_map(|v| {
                            other
                                .0
                                .iter()
                                .find(|(vv, _)| *vv == v)
                                .map(|(vv, &p)| (vv.clone(), p))
                        })
                        .collect(),
                );
                match self_tier.grevlex(&other_tier) {
                    Ordering::Equal => continue,
                    ord => return ord,
                }
            }
        }

        Ordering::Equal
    }
}

impl<E: TieredElimStrategy> PartialOrd for TieredElimMono<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
