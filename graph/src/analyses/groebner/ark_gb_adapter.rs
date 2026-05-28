//! Adapter that hosts ark-gb's Gröbner-basis engine inside zippel.
//!
//! Routes zippel `SparsePolynomial`s through ark-gb's `compute_gb`,
//! which is ~10000× faster than the in-tree Buchberger implementation
//! on Katsura/Cyclic-n.
//!
//! # Layout
//!
//! Two adapter entry points:
//!
//! * [`compute_reduced_gb_grevlex`] — for `GrevLexTerm`. Uses ark-gb's
//!   built-in `ArkGrev<W>`; var-index assignment is just sorted-PRef
//!   order.
//!
//! * [`compute_reduced_gb_elim`] — for `ElimTerm`. Uses an ark-gb
//!   monomial wrapper [`ZippelElimMono`] whose `Ord` and `cmp_key` are
//!   overridden to implement zippel's block-elimination order:
//!   `(elim_block_grevlex, keep_block_grevlex)` lex.
//!
//!   The block-elim encoding relies on **var-index reordering**: eliminated
//!   `PRef`s get *high* ark-gb indices (which sit at MSB byte positions in
//!   ark-gb's packing), so ark-gb's natural degrevlex byte order already
//!   gives the within-block reverse-lex tiebreak in the right blocks. The
//!   only override needed is to put `elim_block_total_degree` into
//!   `cmp_key`'s `pre_key`, which makes the lex compare start on the
//!   elim block.
//!
//! # Conversion outline (one adapter call)
//!
//! 1. Collect the union of `PRef`s used in `input`.
//! 2. Partition (elim path only) and assign ark-gb indices `0..nvars`.
//! 3. Build `Arc<Ring<F, W>>` (W = 128 ⇒ ≤ 1023 variables).
//! 4. Convert each `SparsePolynomial` to `ark_gb::Poly<F, M, W>`.
//! 5. Call `ark_gb::compute_gb(ring, polys)`.
//! 6. Convert the result back to zippel's `Vec<SparsePolynomial<F, T>>`.
//!
//! # Limits
//!
//! The W packing supports `W * 8 - 1` variables and per-var exponents ≤ 127.
//! Inputs exceeding either bound panic with a clear message.
//! Inputs whose union of `PRef`s is empty are handled inline (all-constant
//! polynomials → the unit ideal `[1]` if any constant is nonzero, else
//! the empty basis).
//!
//! # Threading
//!
//! [`compute_reduced_gb_elim`] uses a thread-local mask and therefore calls
//! ark-gb's serial driver directly. This keeps elim ordering independent of
//! the process-wide `ARK_GB_THREADS` setting. The `GrevLexTerm` path has no
//! thread-local ordering state and still uses ark-gb's env-dispatched
//! `compute_gb`.

use std::cell::Cell;
use std::sync::Arc;

use ark_ff::Field;
use ark_gb::monomial::{GrevLexTerm as ArkGrev, MonoTerm as ArkMono, Monomial as ArkMonomial};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;
use share::{Ctx, Set};

use crate::PRef;
use crate::analyses::groebner::monomial::{
    ElimTerm, GrevLexTerm, MonoTerm as ZipMonoTerm, Monomial as ZipMonomial,
};
use crate::analyses::groebner::sparsepoly::SparsePolynomial;

/// Max per-variable exponent ark-gb's 7-bit packing supports.
const MAX_EXPONENT: usize = 127;

/// Compute the max variables a given W layout can represent.
pub(crate) const fn max_vars_for_w(w: usize) -> usize {
    w * 8 - 1
}

// ---------------------------------------------------------------------------
// Shim trait: borrow the underlying zippel `MonoTerm` from either of the
// two zippel monomial wrappers. Defined locally so we don't have to extend
// the public `Monomial` trait in `monomial.rs`.
// ---------------------------------------------------------------------------

/// Adapter-local accessor for the underlying zippel `MonoTerm` map.
///
/// Implemented for `GrevLexTerm` and `ElimTerm` via their `pub(crate)`
/// `as_mono_term()` inherent methods. This lets the conversion helpers be
/// generic over the zippel term type without exposing `MonoTerm` outside
/// the crate.
trait HasMonoTerm {
    fn as_mono_term(&self) -> &ZipMonoTerm;
}

impl HasMonoTerm for GrevLexTerm {
    #[inline]
    fn as_mono_term(&self) -> &ZipMonoTerm {
        GrevLexTerm::as_mono_term(self)
    }
}

impl HasMonoTerm for ElimTerm {
    #[inline]
    fn as_mono_term(&self) -> &ZipMonoTerm {
        ElimTerm::as_mono_term(self)
    }
}

// ---------------------------------------------------------------------------
// GrevLexTerm path.
// ---------------------------------------------------------------------------

/// `GrevLexTerm` backend: fully parametric on W.
/// Routes through ark-gb's built-in `ArkGrev<W>`.
/// Shared pipeline for computing a reduced Gröbner basis with ark-gb.
///
/// Takes the variable ordering, validation result, and a function that computes the GB given
/// a ring and converted polynomials. This consolidates the common setup
/// and conversion logic between grevlex and elim paths.
fn compute_gb_pipeline<F, T, M, const W: usize, GbFn>(
    input: Vec<SparsePolynomial<F, T>>,
    var_order: Vec<PRef>,
    exponents_fit: bool,
    gb_fn: GbFn,
) -> Vec<SparsePolynomial<F, T>>
where
    F: Field,
    T: ZipMonomial + HasMonoTerm,
    M: ArkMonomial<F, W>,
    GbFn: FnOnce(Arc<Ring<F, W>>, Vec<Poly<F, M, W>>) -> Vec<Poly<F, M, W>>,
{
    let actual_nvars = var_order.len();

    if actual_nvars == 0 {
        return constant_only_basis(&input);
    }

    assert_fits_in_ark_gb::<W>(actual_nvars, exponents_fit);

    let var_index = index_map(&var_order);
    let ring: Arc<Ring<F, W>> = Arc::new(
        Ring::<F, W>::new(actual_nvars as u32).expect("nvars within ark-gb packing layout"),
    );

    let polys: Vec<Poly<F, M, W>> = input
        .into_iter()
        .map(|p| zippel_poly_to_ark_gb::<F, T, M, W>(&ring, &var_index, actual_nvars, p))
        .collect();

    let gb = gb_fn(Arc::clone(&ring), polys);

    let mut out: Vec<SparsePolynomial<F, T>> = gb
        .into_iter()
        .map(|p| ark_gb_to_zippel::<F, T, M, W>(&ring, &var_order, p))
        .collect();
    sort_basis_by_zippel_lt(&mut out);
    out
}

pub(crate) fn compute_reduced_gb_grevlex<F: Field, const W: usize>(
    _num_vars: usize,
    input: Vec<SparsePolynomial<F, GrevLexTerm>>,
) -> Vec<SparsePolynomial<F, GrevLexTerm>> {
    let (vars, exponents_fit) = collect_and_validate(&input);
    let var_order: Vec<PRef> = vars.iter().cloned().collect();
    compute_gb_pipeline::<F, GrevLexTerm, ArkGrev<W>, W, _>(
        input,
        var_order,
        exponents_fit,
        |ring, polys| ark_gb::compute_gb::<F, ArkGrev<W>, W>(ring, polys),
    )
}

// ---------------------------------------------------------------------------
// ElimTerm path.
// ---------------------------------------------------------------------------

thread_local! {
    /// Per-byte elim mask for W=8 layouts (up to 63 variables).
    static ELIM_BYTE_MASK_W8: Cell<[u64; 8]> = const { Cell::new([0u64; 8]) };
    /// Per-byte elim mask for W=16 layouts (up to 127 variables).
    static ELIM_BYTE_MASK_W16: Cell<[u64; 16]> = const { Cell::new([0u64; 16]) };
    /// Per-byte elim mask for W=128 layouts (up to 1023 variables).
    static ELIM_BYTE_MASK_W128: Cell<[u64; 128]> = const { Cell::new([0u64; 128]) };
}

/// Get the current elim mask from thread-local storage.
#[inline]
fn get_elim_mask<const W: usize>() -> [u64; W] {
    match W {
        8 => {
            let mut result = [0u64; W];
            ELIM_BYTE_MASK_W8.with(|c| {
                let mask = c.get();
                result.copy_from_slice(&mask);
            });
            result
        }
        16 => {
            let mut result = [0u64; W];
            ELIM_BYTE_MASK_W16.with(|c| {
                let mask = c.get();
                result.copy_from_slice(&mask);
            });
            result
        }
        128 => {
            let mut result = [0u64; W];
            ELIM_BYTE_MASK_W128.with(|c| {
                let mask = c.get();
                result.copy_from_slice(&mask);
            });
            result
        }
        _ => panic!("Unsupported W={W} for elim mask"),
    }
}

/// Set the elim mask in thread-local storage.
#[inline]
fn set_elim_mask<const W: usize>(mask: &[u64; W]) {
    match W {
        8 => {
            let mut m = [0u64; 8];
            m.copy_from_slice(mask);
            ELIM_BYTE_MASK_W8.with(|c| c.set(m));
        }
        16 => {
            let mut m = [0u64; 16];
            m.copy_from_slice(mask);
            ELIM_BYTE_MASK_W16.with(|c| c.set(m));
        }
        128 => {
            let mut m = [0u64; 128];
            m.copy_from_slice(mask);
            ELIM_BYTE_MASK_W128.with(|c| c.set(m));
        }
        _ => panic!("Unsupported W={W} for elim mask"),
    }
}

/// RAII guard that installs an elim-byte-mask for the duration of a
/// `compute_reduced_gb_elim` call, restoring the previous mask on drop.
/// Generic over W to support W=8, W=16, and W=128.
struct ElimMaskGuard<const W: usize> {
    prev: [u64; W],
}

impl<const W: usize> ElimMaskGuard<W> {
    fn install(mask: [u64; W]) -> Self {
        let prev = get_elim_mask::<W>();
        set_elim_mask::<W>(&mask);
        Self { prev }
    }
}

impl<const W: usize> Drop for ElimMaskGuard<W> {
    fn drop(&mut self) {
        set_elim_mask::<W>(&self.prev);
    }
}

/// Sum the byte-values of `packed & mask`. With `mask` set to `0x7F` on
/// elim positions and `0` elsewhere, this returns the elim-block total
/// degree.
#[inline]
fn elim_total_deg<const W: usize>(packed: &[u64; W], mask: &[u64; W]) -> u32 {
    let mut total: u32 = 0;
    for word in 0..W {
        let m = packed[word] & mask[word];
        for b in 0..8 {
            total += ((m >> (b * 8)) & 0xFF) as u32;
        }
    }
    total
}

/// ark-gb monomial wrapper implementing zippel's block-elimination order.
/// Generic over W to support W=8, W=16, and W=128 layouts.
///
/// `cmp` and `cmp_key`:
/// * `cmp` reads the byte-mask from the appropriate thread_local (set by the
///   active `ElimMaskGuard<W>`) to compute the elim-block total degree;
///   if it ties, falls through to ark-gb's full degrevlex on the
///   underlying packed bytes.
/// * `cmp_key` puts `elim_total_deg` into `pre_key` and the standard
///   degrevlex-XOR'd packed words into the suffix. Because the adapter
///   assigns elim `PRef`s to *high* ark-gb indices (i.e. MSB byte
///   positions), the natural degrevlex byte-order tiebreak gives
///   "elim block rev-lex first, then keep block rev-lex" — the exact
///   ordering zippel's [`ElimTerm`] produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ZippelElimMono<const W: usize>(ArkMono<W>);

impl<const W: usize> From<ArkMono<W>> for ZippelElimMono<W> {
    fn from(m: ArkMono<W>) -> Self {
        ZippelElimMono(m)
    }
}

impl<const W: usize> PartialOrd for ZippelElimMono<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const W: usize> Ord for ZippelElimMono<W> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        let mask = get_elim_mask::<W>();
        let a_elim = elim_total_deg::<W>(self.0.packed(), &mask);
        let b_elim = elim_total_deg::<W>(other.0.packed(), &mask);
        match a_elim.cmp(&b_elim) {
            Ordering::Equal => {}
            ord => return ord,
        }
        // Tiebreak: ark-gb's full degrevlex on the same packed bytes.
        ArkGrev::<W>::from(self.0).cmp(&ArkGrev::<W>::from(other.0))
    }
}

impl<F: Field, const W: usize> ArkMonomial<F, W> for ZippelElimMono<W> {
    #[inline]
    fn one(ring: &Ring<F, W>) -> Self {
        ZippelElimMono(ArkMono::<W>::one(ring))
    }
    #[inline]
    fn from_exponents(ring: &Ring<F, W>, exps: &[u32]) -> Option<Self> {
        ArkMono::<W>::from_exponents(ring, exps).map(ZippelElimMono)
    }
    #[inline]
    fn exponent(&self, ring: &Ring<F, W>, i: u32) -> Option<u32> {
        self.0.exponent(ring, i)
    }
    #[inline]
    fn exponents(&self, ring: &Ring<F, W>) -> Vec<u32> {
        self.0.exponents(ring)
    }
    #[inline]
    fn total_deg(&self, _ring: &Ring<F, W>) -> u32 {
        self.0.total_deg()
    }
    #[inline]
    fn mul(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        ZippelElimMono(self.0.mul(&other.0, ring))
    }
    #[inline]
    fn divides(&self, other: &Self, ring: &Ring<F, W>) -> bool {
        self.0.divides(&other.0, ring)
    }
    #[inline]
    fn div(&self, other: &Self, ring: &Ring<F, W>) -> Option<Self> {
        self.0.div(&other.0, ring).map(ZippelElimMono)
    }
    #[inline]
    fn lcm(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        ZippelElimMono(self.0.lcm(&other.0, ring))
    }
    #[inline]
    fn as_mono_term(&self) -> &ArkMono<W> {
        &self.0
    }

    fn cmp_key(packed: &ArkMono<W>, ring: &Ring<F, W>) -> (u64, [u64; W]) {
        // `pre_key` = elim-block total degree (puts the elim block first
        // in lex compare). The suffix is ark-gb's standard degrevlex
        // XOR-flipped packed bytes; since the adapter assigned elim
        // `PRef`s to high ark-gb indices, the natural byte order gives
        // the within-block reverse-lex tiebreak in the correct blocks.
        let mask = get_elim_mask::<W>();
        let elim_deg = elim_total_deg::<W>(packed.packed(), &mask) as u64;
        let flip = ring.cmp_flip_mask();
        let key: [u64; W] = std::array::from_fn(|i| packed.packed()[i] ^ flip[i]);
        (elim_deg, key)
    }
}

/// `ElimTerm` backend: fully parametric on W.
/// Routes to ark-gb with elim-aware monomial ordering.
pub(crate) fn compute_reduced_gb_elim<F: Field, const W: usize>(
    _num_vars: usize,
    input: Vec<SparsePolynomial<F, ElimTerm>>,
) -> Vec<SparsePolynomial<F, ElimTerm>> {
    // Partition PRefs into keep (low ark-gb indices) and elim (high indices).
    let (keep_vars, elim_vars, exponents_fit) = collect_vars_elim(&input);
    let actual_nvars = keep_vars.len() + elim_vars.len();

    if actual_nvars == 0 {
        return constant_only_basis(&input);
    }

    assert_fits_in_ark_gb::<W>(actual_nvars, exponents_fit);

    // Var order: keeps at indices [0, |keep|), elims at [|keep|, nvars).
    // Eliminated PRefs at high indices map to high byte positions in
    // ark-gb's packing; ark-gb's degrevlex then orders elim-rev-lex
    // before keep-rev-lex automatically. The only thing left for the
    // adapter is to put `elim_total_deg` in front via `cmp_key`.
    let mut var_order: Vec<PRef> = Vec::with_capacity(actual_nvars);
    var_order.extend(keep_vars.iter().cloned());
    var_order.extend(elim_vars.iter().cloned());
    let var_index = index_map(&var_order);

    let ring: Arc<Ring<F, W>> = Arc::new(
        Ring::<F, W>::new(actual_nvars as u32).expect("nvars within ark-gb packing layout"),
    );

    // Guard must be active during both conversion and GB computation
    let _guard =
        ElimMaskGuard::<W>::install(build_elim_byte_mask::<W>(keep_vars.len(), actual_nvars));

    let polys: Vec<Poly<F, ZippelElimMono<W>, W>> = input
        .into_iter()
        .map(|p| {
            zippel_poly_to_ark_gb::<F, ElimTerm, ZippelElimMono<W>, W>(
                &ring,
                &var_index,
                actual_nvars,
                p,
            )
        })
        .collect();

    let gb = ark_gb::bba::compute_gb_serial::<F, ZippelElimMono<W>, W>(Arc::clone(&ring), polys);

    let mut out: Vec<SparsePolynomial<F, ElimTerm>> = gb
        .into_iter()
        .map(|p| ark_gb_to_zippel::<F, ElimTerm, ZippelElimMono<W>, W>(&ring, &var_order, p))
        .collect();
    sort_basis_by_zippel_lt(&mut out);
    out
}

pub(crate) fn collect_vars_elim<F: Field>(
    input: &[SparsePolynomial<F, ElimTerm>],
) -> (Vec<PRef>, Vec<PRef>, bool) {
    let (vars, exponents_fit) = collect_and_validate(input);
    let mut keep: Vec<PRef> = Vec::new();
    let mut elim: Vec<PRef> = Vec::new();
    for v in vars.iter().cloned() {
        if ElimTerm::eliminate_var(&v) {
            elim.push(v);
        } else {
            keep.push(v);
        }
    }
    (keep, elim, exponents_fit)
}

/// Build the byte mask that marks ark-gb byte positions corresponding
/// to elim vars. With elim vars at ark-gb indices `[num_keep, nvars)`,
/// their byte positions are `byte_index_for_var(nvars, i) = i + (W*8 - 1) - nvars`
/// for `i ∈ [num_keep, nvars)`. We OR `0x7F` into those byte slots.
fn build_elim_byte_mask<const W: usize>(num_keep: usize, nvars: usize) -> [u64; W] {
    let mut mask = [0u64; W];
    for i in num_keep..nvars {
        let byte_idx = i + W * 8 - 1 - nvars;
        let word = byte_idx / 8;
        let shift = (byte_idx % 8) * 8;
        mask[word] |= 0x7Fu64 << shift;
    }
    mask
}

// ---------------------------------------------------------------------------
// Shared helpers (generic over zippel term type T and ark-gb monomial M).
// ---------------------------------------------------------------------------

/// Union of `PRef`s appearing in any term of any input polynomial. Shared
/// by both backend paths; the elim path additionally partitions the result
/// on `ElimTerm::eliminate_var`.
/// Collect all PRef variables and validate exponents in a single traversal.
/// Returns (variable_set, exponents_fit).
fn collect_and_validate<F: Field, T: ZipMonomial + HasMonoTerm>(
    input: &[SparsePolynomial<F, T>],
) -> (Set<PRef>, bool) {
    let mut vars: Set<PRef> = Set::new();
    let mut exponents_fit = true;
    for p in input {
        for (term, _) in p.terms.iter() {
            for v in term.vars() {
                vars.insert(v);
            }
            if exponents_fit {
                for (_, &e) in term.as_mono_term().iter_pairs() {
                    if e > MAX_EXPONENT {
                        exponents_fit = false;
                        break;
                    }
                }
            }
        }
    }
    (vars, exponents_fit)
}

/// Convert a zippel polynomial (in the term type `T`) to an ark-gb polynomial
/// (in the ark-gb monomial type `M`). Caller guarantees every `PRef` in the
/// term is present in `var_index`, and per-variable exponents fit (checked
/// by `exponents_fit` before invocation).
fn zippel_poly_to_ark_gb<
    F: Field,
    T: ZipMonomial + HasMonoTerm,
    M: ArkMonomial<F, W>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    var_index: &Ctx<PRef, usize>,
    nvars: usize,
    p: SparsePolynomial<F, T>,
) -> Poly<F, M, W> {
    let pairs: Vec<(F, M)> = p
        .terms
        .iter()
        .map(|(term, coeff)| {
            let mut exps = vec![0u32; nvars];
            for (v, &e) in term.as_mono_term().iter_pairs() {
                let idx = *var_index
                    .get(v)
                    .expect("every PRef in input was collected into var_index");
                exps[idx] = e as u32;
            }
            let mono = M::from_exponents(ring, &exps)
                .expect("exponents within ark-gb 7-bit budget (pre-checked)");
            (*coeff, mono)
        })
        .collect();
    Poly::from_terms(ring, pairs)
}

/// Convert an ark-gb polynomial back to a zippel polynomial in the term
/// type `T`. `T: From<Vec<(PRef, usize)>>` is implied by the `Monomial`
/// supertrait, so the bound is automatic.
fn ark_gb_to_zippel<F: Field, T: ZipMonomial, M: ArkMonomial<F, W>, const W: usize>(
    ring: &Ring<F, W>,
    var_order: &[PRef],
    p: Poly<F, M, W>,
) -> SparsePolynomial<F, T> {
    let mut terms: Ctx<T, F> = Ctx::new();
    for (coeff, mono) in p.iter() {
        let exps = mono.exponents(ring);
        let pairs: Vec<(PRef, usize)> = exps
            .iter()
            .enumerate()
            .filter_map(|(i, &e)| {
                if e == 0 {
                    None
                } else {
                    Some((var_order[i].clone(), e as usize))
                }
            })
            .collect();
        let zterm: T = T::from(pairs);
        terms.insert(&zterm, &coeff);
    }
    SparsePolynomial { terms }
}

fn index_map(var_order: &[PRef]) -> Ctx<PRef, usize> {
    var_order
        .iter()
        .enumerate()
        .fold(Ctx::new(), |mut acc, (i, v)| {
            acc.insert(v, &i);
            acc
        })
}

/// Assert that the input fits ark-gb's `W` layout (≤ max_vars variables,
/// all exponents ≤ 127). Panics with a clear diagnostic if not.
/// Caller has already handled the `actual_nvars == 0` (constant-only) case.
fn assert_fits_in_ark_gb<const W: usize>(actual_nvars: usize, exponents_ok: bool) {
    let max_vars = max_vars_for_w(W);
    assert!(
        actual_nvars <= max_vars,
        "input has {actual_nvars} variables; ark-gb's W={W} layout supports ≤ {max_vars}. \
         Bump W or file an issue if you need support for larger problems."
    );
    assert!(
        exponents_ok,
        "input has a per-variable exponent exceeding {MAX_EXPONENT}; \
         ark-gb's 7-bit packing can't represent it."
    );
}

/// All-constant input → unit ideal `[1]` if any constant is nonzero,
/// else the empty basis. Independent of `T`.
fn constant_only_basis<F: Field, T: ZipMonomial>(
    input: &[SparsePolynomial<F, T>],
) -> Vec<SparsePolynomial<F, T>> {
    let nonzero = input.iter().any(|p| !p.is_zero());
    if nonzero {
        vec![SparsePolynomial::lit(&F::one())]
    } else {
        Vec::new()
    }
}

/// Sort the basis in zippel's canonical order: ascending by leading
/// term under `T::cmp` (the same sort used by the test-only legacy
/// reducer). ark-gb's internal sort uses ark-gb's `Ord` on
/// the wrapper monomial, which agrees with `T::cmp` *up to* leading
/// convention; this re-sort makes the basis Vec match the legacy
/// output element-by-element.
fn sort_basis_by_zippel_lt<F: Field, T: ZipMonomial>(basis: &mut [SparsePolynomial<F, T>]) {
    basis.sort_by(|p1, p2| {
        let lt1 = p1.leading_term().map(|(_, t)| t);
        let lt2 = p2.leading_term().map(|(_, t)| t);
        lt1.cmp(&lt2)
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use backend::ATyp;
    use lang::typ::{Distribution, Qualifier};
    use petgraph::graph::NodeIndex;

    #[test]
    fn elim_adapter_supports_w128_with_more_than_127_variables() {
        let vars = (0..130)
            .map(|i| {
                PRef::from_node(
                    NodeIndex::new(i + 1),
                    ATyp::scalar(),
                    0,
                    Qualifier::Local,
                    Distribution::Nonuniform,
                )
            })
            .map(|v| (v, 1usize))
            .collect::<Vec<_>>();
        let product = ElimTerm::from(vars);
        let polynomial = SparsePolynomial::from(vec![(&product, Fr::from(1u64))]);

        let basis = compute_reduced_gb_elim::<Fr, 128>(130, vec![polynomial]);

        assert_eq!(basis.len(), 1);
    }
}
