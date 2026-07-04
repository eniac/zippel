//! Adapter that hosts ark-gb's Gröbner-basis engine inside zippel.
//!
//! Routes zippel `Polynomial<F>`s through ark-gb's `compute_gb`,
//! which is ~10000× faster than the in-tree Buchberger implementation
//! on Katsura/Cyclic-n.
//!
//! # Layout
//!
//! Two adapter entry points:
//!
//! * [`compute_reduced_gb_grevlex`] — single GrevLex block. Uses ark-gb's
//!   built-in `ArkGrev<W>`; var-index assignment is just sorted-PRef
//!   order.
//!
//! * [`compute_reduced_gb_with_elim`] — 2-block GrevLex/GrevLex (elim).
//!   Uses an ark-gb monomial wrapper [`ZippelElimMono`] whose `Ord` and
//!   `cmp_key` overridden to implement block-elimination order.
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
//! 4. Convert each `Polynomial<F>` to `ark_gb::Poly<F, M, W>`.
//! 5. Call `ark_gb::compute_gb(ring, polys)`.
//! 6. Convert the result back to `Vec<Polynomial<F>>`.
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
//! [`compute_reduced_gb_with_elim`] uses a thread-local mask and therefore calls
//! ark-gb's serial driver directly. This keeps elim ordering independent of
//! the process-wide `ARK_GB_THREADS` setting. The GrevLex path has no
//! thread-local ordering state and still uses ark-gb's env-dispatched
//! `compute_gb`.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::sync::Arc;

use ark_ff::Field;
use ark_gb::monomial::{GrevLexTerm as ArkGrev, MonoTerm as ArkMono, Monomial as ArkMonomial};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;
use share::{Ctx, Set};

use crate::PRef;
use crate::frontend::{Monomial, Polynomial};

/// Max per-variable exponent ark-gb's 7-bit packing supports.
const MAX_EXPONENT: usize = 127;

/// Compute the max variables a given W layout can represent.
pub(crate) const fn max_vars_for_w(w: usize) -> usize {
    w * 8 - 1
}

// ---------------------------------------------------------------------------
// GrevLex path.
// ---------------------------------------------------------------------------

/// Shared pipeline for computing a reduced Gröbner basis with ark-gb.
///
/// Takes the variable ordering, validation result, and a function that computes the GB given
/// a ring and converted polynomials. This consolidates the common setup
/// and conversion logic between grevlex and elim paths.
pub(crate) fn compute_gb_pipeline<F, M, const W: usize, GbFn>(
    input: Vec<Polynomial<F>>,
    var_order: Vec<PRef>,
    exponents_fit: bool,
    gb_fn: GbFn,
) -> Vec<Polynomial<F>>
where
    F: Field,
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
        .map(|p| poly_to_ark_gb::<F, M, W>(&ring, &var_index, actual_nvars, p))
        .collect();

    let gb = gb_fn(Arc::clone(&ring), polys);

    gb.into_iter()
        .map(|p| ark_gb_to_poly::<F, M, W>(&ring, &var_order, p))
        .collect()
}

pub(crate) fn compute_reduced_gb_grevlex<F: Field, const W: usize>(
    input: Vec<Polynomial<F>>,
) -> Vec<Polynomial<F>> {
    let (vars, exponents_fit) = collect_and_validate(&input);
    let var_order: Vec<PRef> = vars.iter().cloned().collect();
    compute_gb_pipeline::<F, ArkGrev<W>, W, _>(input, var_order, exponents_fit, |ring, polys| {
        ark_gb::compute_gb::<F, ArkGrev<W>, W>(ring, polys)
    })
}

// ---------------------------------------------------------------------------
// ElimMono path.
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
/// `compute_reduced_gb_with_elim` call, restoring the previous mask on drop.
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
///   ordering zippel's [`ElimMono`] produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ZippelElimMono<const W: usize>(ArkMono<W>);

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

/// Generic elim-ordering backend, parametric on W.
/// Routes to ark-gb with elim-aware monomial ordering.
pub(crate) fn compute_reduced_gb_with_elim<F: Field, const W: usize>(
    input: Vec<Polynomial<F>>,
    eliminate_fn: &dyn Fn(&PRef) -> bool,
) -> Vec<Polynomial<F>> {
    let (keep_vars, elim_vars, exponents_fit) = collect_vars_with(&input, eliminate_fn);
    let actual_nvars = keep_vars.len() + elim_vars.len();

    if actual_nvars == 0 {
        return constant_only_basis(&input);
    }

    assert_fits_in_ark_gb::<W>(actual_nvars, exponents_fit);

    let mut var_order: Vec<PRef> = Vec::with_capacity(actual_nvars);
    var_order.extend(keep_vars.iter().cloned());
    var_order.extend(elim_vars.iter().cloned());

    let _guard =
        ElimMaskGuard::<W>::install(build_elim_byte_mask::<W>(keep_vars.len(), actual_nvars));

    compute_gb_pipeline::<F, ZippelElimMono<W>, W, _>(
        input,
        var_order,
        exponents_fit,
        |ring, polys| ark_gb::bba::compute_gb_serial::<F, ZippelElimMono<W>, W>(ring, polys),
    )
}

fn collect_vars_with<F: Field>(
    input: &[Polynomial<F>],
    eliminate_fn: &dyn Fn(&PRef) -> bool,
) -> (Vec<PRef>, Vec<PRef>, bool) {
    let (vars, exponents_fit) = collect_and_validate(input);
    let mut keep: Vec<PRef> = Vec::new();
    let mut elim: Vec<PRef> = Vec::new();
    for v in vars.iter().cloned() {
        if eliminate_fn(&v) {
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

/// Collect all PRef variables from input polynomials and validate exponents.
/// Returns (variable_set, exponents_fit).
pub(crate) fn collect_and_validate<F: Field>(input: &[Polynomial<F>]) -> (Set<PRef>, bool) {
    let mut vars: Set<PRef> = Set::new();
    let mut exponents_fit = true;
    for p in input {
        for mono in p.terms.keys() {
            for (v, &e) in mono.iter() {
                vars.insert(v.clone());
                if exponents_fit && e > MAX_EXPONENT {
                    exponents_fit = false;
                }
            }
        }
    }
    (vars, exponents_fit)
}

/// Convert a zippel `Polynomial<F>` to an ark-gb polynomial in monomial type `M`.
fn poly_to_ark_gb<F: Field, M: ArkMonomial<F, W>, const W: usize>(
    ring: &Ring<F, W>,
    var_index: &Ctx<PRef, usize>,
    nvars: usize,
    p: Polynomial<F>,
) -> Poly<F, M, W> {
    let pairs: Vec<(F, M)> = p
        .terms
        .iter()
        .map(|(mono, coeff)| {
            let mut exps = vec![0u32; nvars];
            for (v, &e) in mono.iter() {
                let idx = *var_index
                    .get(v)
                    .expect("every PRef in input was collected into var_index");
                exps[idx] = e as u32;
            }
            let m = M::from_exponents(ring, &exps)
                .expect("exponents within ark-gb 7-bit budget (pre-checked)");
            (*coeff, m)
        })
        .collect();
    Poly::from_terms(ring, pairs)
}

/// Convert an ark-gb polynomial back to a zippel `Polynomial<F>`.
fn ark_gb_to_poly<F: Field, M: ArkMonomial<F, W>, const W: usize>(
    ring: &Ring<F, W>,
    var_order: &[PRef],
    p: Poly<F, M, W>,
) -> Polynomial<F> {
    let mut terms: HashMap<Monomial, F> = HashMap::new();
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
        terms.insert(Monomial::from(pairs), coeff);
    }
    Polynomial { terms }
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
pub(crate) fn assert_fits_in_ark_gb<const W: usize>(actual_nvars: usize, exponents_ok: bool) {
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
/// else the empty basis.
pub(crate) fn constant_only_basis<F: Field>(input: &[Polynomial<F>]) -> Vec<Polynomial<F>> {
    let nonzero = input.iter().any(|p| !p.is_zero());
    if nonzero {
        vec![Polynomial::lit(&F::one())]
    } else {
        Vec::new()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TierKind {
    Lex,
    GrevLex,
}

#[derive(Clone)]
#[allow(dead_code)]
struct TierBlock {
    raw_tier: usize,
    start: usize,
    len: usize,
    kind: TierKind,
    counts: Option<BoundedCompositionTable>,
}

impl TierBlock {
    fn indices(&self) -> impl Iterator<Item = usize> {
        self.start..self.start + self.len
    }
}

#[derive(Clone)]
#[allow(dead_code)]
pub(crate) struct TierLayout {
    nvars: usize,
    tiers: Vec<TierBlock>,
    key_bits: usize,
}

#[derive(Clone)]
#[allow(dead_code)]
struct BoundedCompositionTable {
    k: usize,
    max_sum: usize,
    table_u64: Option<Vec<Vec<u64>>>,
    table_biguint: Option<Vec<Vec<num_bigint::BigUint>>>,
}

impl BoundedCompositionTable {
    fn new(k: usize, max_entry: usize) -> Self {
        let max_sum = max_entry * k;
        let mut table = vec![vec![0u64; max_sum + 1]; k + 1];
        table[0][0] = 1;
        for slot in table[1].iter_mut().take(max_sum.min(max_entry) + 1) {
            *slot = 1;
        }
        let mut overflow = false;
        for n in 2..=k {
            let mut prefix = vec![0u64; max_sum + 2];
            prefix[0] = table[n - 1][0];
            for s in 1..=max_sum {
                prefix[s] = match prefix[s - 1].checked_add(table[n - 1][s]) {
                    Some(v) => v,
                    None => {
                        overflow = true;
                        u64::MAX
                    }
                };
            }
            for s in 0..=max_sum {
                let lo = s.saturating_sub(max_entry);
                if lo == 0 {
                    table[n][s] = prefix[s];
                } else {
                    table[n][s] = prefix[s].saturating_sub(prefix[lo - 1]);
                }
            }
        }
        if overflow {
            return Self::new_biguint(k, max_entry);
        }
        BoundedCompositionTable {
            k,
            max_sum,
            table_u64: Some(table),
            table_biguint: None,
        }
    }

    fn new_biguint(k: usize, max_entry: usize) -> Self {
        use num_bigint::BigUint;
        let max_sum = max_entry * k;
        let mut table = vec![vec![BigUint::ZERO; max_sum + 1]; k + 1];
        table[0][0] = BigUint::from(1u64);
        for slot in table[1].iter_mut().take(max_sum.min(max_entry) + 1) {
            *slot = BigUint::from(1u64);
        }
        let mut prefix = vec![BigUint::ZERO; max_sum + 2];
        for n in 2..=k {
            prefix[0] = table[n - 1][0].clone();
            for s in 1..=max_sum {
                prefix[s] = &prefix[s - 1] + &table[n - 1][s];
            }
            for s in 0..=max_sum {
                let lo = s.saturating_sub(max_entry);
                if lo == 0 {
                    table[n][s] = prefix[s].clone();
                } else {
                    table[n][s] = &prefix[s] - &prefix[lo - 1];
                }
            }
        }
        BoundedCompositionTable {
            k,
            max_sum,
            table_u64: None,
            table_biguint: Some(table),
        }
    }

    fn count(&self, n: usize, sum: usize) -> num_bigint::BigUint {
        if sum > self.max_sum {
            return num_bigint::BigUint::ZERO;
        }
        if let Some(ref table) = self.table_u64 {
            num_bigint::BigUint::from(table[n][sum])
        } else {
            self.table_biguint.as_ref().unwrap()[n][sum].clone()
        }
    }
}

pub(crate) fn build_tier_layout<const W: usize>(
    group_lens: &[(usize, usize)],
    nvars: usize,
) -> TierLayout {
    let mut start = 0;
    let mut tiers = Vec::new();

    for (normalized_idx, &(raw_tier, len)) in group_lens.iter().enumerate() {
        if len == 0 {
            continue;
        }

        let kind = if normalized_idx == 0 && raw_tier == 0 {
            TierKind::Lex
        } else {
            TierKind::GrevLex
        };

        let counts = (kind == TierKind::GrevLex).then(|| BoundedCompositionTable::new(len, 127));

        tiers.push(TierBlock {
            raw_tier,
            start,
            len,
            kind,
            counts,
        });
        start += len;
    }

    let key_bits = tiers.iter().map(|t| 7 * t.len).sum();
    debug_assert_eq!(start, nvars);
    debug_assert!(key_bits <= 64 * (W + 1));

    TierLayout {
        nvars,
        tiers,
        key_bits,
    }
}

thread_local! {
    static TIER_LAYOUT_W8: RefCell<Option<TierLayout>> = const { RefCell::new(None) };
    static TIER_LAYOUT_W16: RefCell<Option<TierLayout>> = const { RefCell::new(None) };
    static TIER_LAYOUT_W128: RefCell<Option<TierLayout>> = const { RefCell::new(None) };
}

fn get_tier_layout<const W: usize>() -> TierLayout {
    match W {
        8 => TIER_LAYOUT_W8.with(|c| c.borrow().clone().unwrap()),
        16 => TIER_LAYOUT_W16.with(|c| c.borrow().clone().unwrap()),
        128 => TIER_LAYOUT_W128.with(|c| c.borrow().clone().unwrap()),
        _ => panic!("Unsupported W={W} for tiered elim"),
    }
}

fn replace_tier_layout<const W: usize>(layout: Option<TierLayout>) -> Option<TierLayout> {
    match W {
        8 => TIER_LAYOUT_W8.with(|c| std::mem::replace(&mut *c.borrow_mut(), layout)),
        16 => TIER_LAYOUT_W16.with(|c| std::mem::replace(&mut *c.borrow_mut(), layout)),
        128 => TIER_LAYOUT_W128.with(|c| std::mem::replace(&mut *c.borrow_mut(), layout)),
        _ => panic!("Unsupported W={W} for tiered elim"),
    }
}

pub(crate) struct TierLayoutGuard<const W: usize> {
    prev: Option<TierLayout>,
}

impl<const W: usize> TierLayoutGuard<W> {
    pub(crate) fn install(layout: TierLayout) -> Self {
        let prev = replace_tier_layout::<W>(Some(layout));
        Self { prev }
    }
}

impl<const W: usize> Drop for TierLayoutGuard<W> {
    fn drop(&mut self) {
        replace_tier_layout::<W>(self.prev.take());
    }
}

struct OrderedKey<const W: usize> {
    pre_key: u64,
    cmp_key: [u64; W],
    bit_len: usize,
}

impl<const W: usize> OrderedKey<W> {
    fn new() -> Self {
        OrderedKey {
            pre_key: 0,
            cmp_key: [0u64; W],
            bit_len: 0,
        }
    }

    fn push_bit(&mut self, bit: bool) {
        let chunk = self.bit_len / 64;
        let offset = self.bit_len % 64;
        debug_assert!(chunk <= W);
        if bit {
            let mask = 1u64 << (63 - offset);
            if chunk == 0 {
                self.pre_key |= mask;
            } else {
                self.cmp_key[W - chunk] |= mask;
            }
        }
        self.bit_len += 1;
    }

    fn push_7bit(&mut self, value: u8) {
        debug_assert!(value < 128);
        for shift in (0..7).rev() {
            self.push_bit(((value >> shift) & 1) != 0);
        }
    }

    fn push_bits(&mut self, words: &[u64], bits: usize) {
        if bits == 0 {
            return;
        }
        let total_words = bits.div_ceil(64);
        debug_assert!(words.len() >= total_words);
        let leading_zeros = total_words * 64 - bits;
        for bi in 0..bits {
            let abs_bit = leading_zeros + bi;
            let wi = abs_bit / 64;
            let shift = 63 - (abs_bit % 64);
            let bit_val = ((words[wi] >> shift) & 1) != 0;
            self.push_bit(bit_val);
        }
    }

    fn finish(self) -> (u64, [u64; W]) {
        (self.pre_key, self.cmp_key)
    }
}

fn push_grevlex_rank_bits<const W: usize>(
    key: &mut OrderedKey<W>,
    packed: &ArkMono<W>,
    ring: &Ring<impl Field, W>,
    tier: &TierBlock,
) {
    let exps: Vec<u8> = tier
        .indices()
        .map(|i| packed.exponent(ring, i as u32).unwrap() as u8)
        .collect();
    let k = exps.len();
    let rank_bits = 7 * k;
    if k == 0 {
        return;
    }

    let degree: usize = exps.iter().map(|&e| e as usize).sum();
    let max_degree = 127 * k;

    let mut rank = num_bigint::BigUint::ZERO;

    let counts = tier.counts.as_ref().unwrap();

    for d in (degree + 1)..=max_degree {
        rank += counts.count(k, d);
    }

    let mut fixed_right_sum = 0usize;
    for j in (0..k).rev() {
        let ej = exps[j] as usize;
        for candidate in 0..ej {
            let used = fixed_right_sum + candidate;
            if degree >= used {
                let remaining = degree - used;
                rank += counts.count(j, remaining);
            }
        }
        fixed_right_sum += ej;
    }

    let mut digits = rank.to_u64_digits();
    let needed_words = rank_bits.div_ceil(64);
    digits.resize(needed_words, 0);
    let complement_words: Vec<u64> = digits.into_iter().rev().map(|w| !w).collect();
    key.push_bits(&complement_words, rank_bits);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ZippelTieredElimMono<const W: usize>(ArkMono<W>);

impl<const W: usize> From<ArkMono<W>> for ZippelTieredElimMono<W> {
    fn from(m: ArkMono<W>) -> Self {
        ZippelTieredElimMono(m)
    }
}

impl<const W: usize> PartialOrd for ZippelTieredElimMono<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const W: usize> Ord for ZippelTieredElimMono<W> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        let layout = get_tier_layout::<W>();
        let nvars = layout.nvars;
        let first_byte = W * 8 - 1 - nvars;

        let a_packed = self.0.packed();
        let b_packed = other.0.packed();

        for tier in &layout.tiers {
            match tier.kind {
                TierKind::Lex => {
                    for i in tier.indices() {
                        let byte_pos = first_byte + i;
                        let word = byte_pos / 8;
                        let shift = ((byte_pos % 8) * 8) as u32;
                        let ea = ((a_packed[word] >> shift) & 0x7F) as u32;
                        let eb = ((b_packed[word] >> shift) & 0x7F) as u32;
                        match ea.cmp(&eb) {
                            Ordering::Equal => continue,
                            ord => return ord,
                        }
                    }
                }
                TierKind::GrevLex => {
                    let mut a_deg: u32 = 0;
                    let mut b_deg: u32 = 0;
                    for i in tier.indices() {
                        let byte_pos = first_byte + i;
                        let word = byte_pos / 8;
                        let shift = ((byte_pos % 8) * 8) as u32;
                        a_deg += ((a_packed[word] >> shift) & 0x7F) as u32;
                        b_deg += ((b_packed[word] >> shift) & 0x7F) as u32;
                    }
                    match a_deg.cmp(&b_deg) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                    let a_exps: Vec<u32> = tier
                        .indices()
                        .map(|i| {
                            let byte_pos = first_byte + i;
                            let word = byte_pos / 8;
                            let shift = ((byte_pos % 8) * 8) as u32;
                            ((a_packed[word] >> shift) & 0x7F) as u32
                        })
                        .collect();
                    let b_exps: Vec<u32> = tier
                        .indices()
                        .map(|i| {
                            let byte_pos = first_byte + i;
                            let word = byte_pos / 8;
                            let shift = ((byte_pos % 8) * 8) as u32;
                            ((b_packed[word] >> shift) & 0x7F) as u32
                        })
                        .collect();
                    for j in (0..a_exps.len()).rev() {
                        match a_exps[j].cmp(&b_exps[j]) {
                            Ordering::Equal => continue,
                            ord => return ord.reverse(),
                        }
                    }
                }
            }
        }
        Ordering::Equal
    }
}

impl<F: Field, const W: usize> ArkMonomial<F, W> for ZippelTieredElimMono<W> {
    #[inline]
    fn one(ring: &Ring<F, W>) -> Self {
        ZippelTieredElimMono(ArkMono::<W>::one(ring))
    }
    #[inline]
    fn from_exponents(ring: &Ring<F, W>, exps: &[u32]) -> Option<Self> {
        ArkMono::<W>::from_exponents(ring, exps).map(ZippelTieredElimMono)
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
        ZippelTieredElimMono(self.0.mul(&other.0, ring))
    }
    #[inline]
    fn divides(&self, other: &Self, ring: &Ring<F, W>) -> bool {
        self.0.divides(&other.0, ring)
    }
    #[inline]
    fn div(&self, other: &Self, ring: &Ring<F, W>) -> Option<Self> {
        self.0.div(&other.0, ring).map(ZippelTieredElimMono)
    }
    #[inline]
    fn lcm(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        ZippelTieredElimMono(self.0.lcm(&other.0, ring))
    }
    #[inline]
    fn as_mono_term(&self) -> &ArkMono<W> {
        &self.0
    }

    fn cmp_key(packed: &ArkMono<W>, ring: &Ring<F, W>) -> (u64, [u64; W]) {
        let layout = get_tier_layout::<W>();
        let mut key = OrderedKey::<W>::new();

        for tier in &layout.tiers {
            match tier.kind {
                TierKind::Lex => {
                    for i in tier.indices() {
                        let exp = packed.exponent(ring, i as u32).unwrap() as u8;
                        key.push_7bit(exp);
                    }
                }
                TierKind::GrevLex => {
                    push_grevlex_rank_bits(&mut key, packed, ring, tier);
                }
            }
        }

        key.finish()
    }
}

#[cfg(test)]
mod tiered_consistency_test {
    use super::*;
    use ark_bls12_381::Fr;

    fn make_layout_and_ring<const W: usize>(
        group_lens: &[(usize, usize)],
    ) -> (TierLayout, Arc<Ring<Fr, W>>) {
        let nvars: usize = group_lens.iter().map(|(_, len)| *len).sum();
        let layout = build_tier_layout::<W>(group_lens, nvars);
        let ring = Arc::new(Ring::<Fr, W>::new(nvars as u32).unwrap());
        (layout, ring)
    }

    fn check_consistency<const W: usize>(
        _layout: &TierLayout,
        ring: &Arc<Ring<Fr, W>>,
        monos: &[ZippelTieredElimMono<W>],
    ) {
        for i in 0..monos.len() {
            for j in 0..monos.len() {
                let ord_result = monos[i].cmp(&monos[j]);
                let key_i = <ZippelTieredElimMono<W> as ArkMonomial<Fr, W>>::cmp_key(
                    <ZippelTieredElimMono<W> as ArkMonomial<Fr, W>>::as_mono_term(&monos[i]),
                    ring,
                );
                let key_j = <ZippelTieredElimMono<W> as ArkMonomial<Fr, W>>::cmp_key(
                    <ZippelTieredElimMono<W> as ArkMonomial<Fr, W>>::as_mono_term(&monos[j]),
                    ring,
                );
                let key_ord = key_i.cmp(&key_j);
                assert_eq!(
                    ord_result, key_ord,
                    "Mismatch at i={}, j={}: Ord={:?}, key_cmp={:?}\n  key_i={:?}\n  key_j={:?}",
                    i, j, ord_result, key_ord, key_i, key_j
                );
            }
        }
    }

    #[test]
    fn test_cmp_key_ord_consistency_w8() {
        let (layout, ring) = make_layout_and_ring::<8>(&[(0, 2), (1, 2)]);
        let _guard = TierLayoutGuard::<8>::install(layout.clone());

        let exps_list: Vec<Vec<u32>> = vec![
            vec![0, 0, 0, 0],
            vec![1, 0, 0, 0],
            vec![0, 1, 0, 0],
            vec![0, 0, 1, 0],
            vec![0, 0, 0, 1],
            vec![1, 1, 0, 0],
            vec![0, 0, 1, 1],
            vec![2, 0, 0, 0],
            vec![0, 2, 0, 0],
            vec![0, 0, 2, 0],
            vec![0, 0, 0, 2],
            vec![1, 0, 1, 0],
            vec![0, 1, 0, 1],
        ];

        let monos: Vec<ZippelTieredElimMono<8>> = exps_list
            .iter()
            .map(|exps| ZippelTieredElimMono::from_exponents(&ring, exps).unwrap())
            .collect();

        check_consistency(&layout, &ring, &monos);
    }

    #[test]
    fn test_cmp_key_ord_consistency_3_tiers() {
        let (layout, ring) = make_layout_and_ring::<8>(&[(0, 1), (1, 2), (2, 1)]);
        let _guard = TierLayoutGuard::<8>::install(layout.clone());

        let mut exps_list: Vec<Vec<u32>> = Vec::new();
        for e0 in 0..=2u32 {
            for e1 in 0..=2u32 {
                for e2 in 0..=2u32 {
                    for e3 in 0..=2u32 {
                        exps_list.push(vec![e0, e1, e2, e3]);
                    }
                }
            }
        }

        let monos: Vec<ZippelTieredElimMono<8>> = exps_list
            .iter()
            .map(|exps| ZippelTieredElimMono::from_exponents(&ring, exps).unwrap())
            .collect();

        check_consistency(&layout, &ring, &monos);
    }

    #[test]
    fn test_cmp_key_ord_consistency_w128_3_tiers() {
        let (layout, ring) = make_layout_and_ring::<128>(&[(0, 2), (1, 3), (2, 2)]);
        let _guard = TierLayoutGuard::<128>::install(layout.clone());

        let mut exps_list: Vec<Vec<u32>> = Vec::new();
        for e0 in 0..=2u32 {
            for e1 in 0..=2u32 {
                for e2 in 0..=2u32 {
                    for e3 in 0..=2u32 {
                        for e4 in 0..=0u32 {
                            for e5 in 0..=0u32 {
                                for e6 in 0..=0u32 {
                                    exps_list.push(vec![e0, e1, e2, e3, e4, e5, e6]);
                                }
                            }
                        }
                    }
                }
            }
        }

        let monos: Vec<ZippelTieredElimMono<128>> = exps_list
            .iter()
            .map(|exps| ZippelTieredElimMono::from_exponents(&ring, exps).unwrap())
            .collect();

        check_consistency(&layout, &ring, &monos);
    }

    #[test]
    fn test_cmp_key_ord_consistency_w128_large_grevlex() {
        let (layout, ring) = make_layout_and_ring::<128>(&[(0, 1), (1, 5)]);
        let _guard = TierLayoutGuard::<128>::install(layout.clone());

        let sample_exps: Vec<Vec<u32>> = vec![
            vec![0, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 1, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![3, 0, 0, 0, 0, 0],
            vec![0, 3, 0, 0, 0, 0],
            vec![0, 0, 3, 0, 0, 0],
            vec![0, 0, 0, 3, 0, 0],
            vec![0, 0, 0, 0, 3, 0],
            vec![0, 0, 0, 0, 0, 3],
            vec![1, 1, 1, 1, 1, 0],
            vec![0, 1, 1, 1, 1, 1],
            vec![2, 2, 2, 0, 0, 0],
            vec![0, 0, 0, 2, 2, 2],
            vec![127, 0, 0, 0, 0, 0],
            vec![0, 127, 0, 0, 0, 0],
            vec![5, 5, 5, 5, 5, 5],
        ];

        let monos: Vec<ZippelTieredElimMono<128>> = sample_exps
            .iter()
            .map(|exps| ZippelTieredElimMono::from_exponents(&ring, exps).unwrap())
            .collect();

        check_consistency(&layout, &ring, &monos);
    }

    #[test]
    fn test_schnorr_layout_key_injection() {
        let (layout, ring) = make_layout_and_ring::<128>(&[(0, 5), (1, 1), (2, 7)]);
        let _guard = TierLayoutGuard::<128>::install(layout.clone());

        let mut key_to_mono: std::collections::HashMap<(u64, [u64; 128]), Vec<u32>> =
            std::collections::HashMap::new();
        let mut exps_list: Vec<Vec<u32>> = Vec::new();
        for e0 in 0..=5u32 {
            for e5 in 0..=5u32 {
                for e6 in 0..=5u32 {
                    for e9 in 0..=5u32 {
                        exps_list.push(vec![e0, 0, 0, 0, 0, e5, e6, 0, 0, e9, 0, 0, 0]);
                    }
                }
            }
        }

        for exps in &exps_list {
            let m = ZippelTieredElimMono::<128>::from_exponents(&ring, exps).unwrap();
            let key = <ZippelTieredElimMono<128> as ArkMonomial<Fr, 128>>::cmp_key(
                <ZippelTieredElimMono<128> as ArkMonomial<Fr, 128>>::as_mono_term(&m),
                &ring,
            );
            if let Some(prev) = key_to_mono.get(&key) {
                if prev != exps {
                    panic!(
                        "KEY COLLISION: key={:?} prev={:?} curr={:?}",
                        key, prev, exps
                    );
                }
            } else {
                key_to_mono.insert(key, exps.clone());
            }
        }
    }
}
