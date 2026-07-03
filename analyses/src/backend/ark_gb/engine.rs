//! ark-gb backend: interprets [`MonoOrder`] and routes through the external
//! ark-gb crate.
//!
//! Supported `MonoOrder` patterns (others return [`BackendError::UnsupportedOrder`]):
//!
//! | Pattern | ark-gb path |
//! |---------|-------------|
//! | `[Block { None, GrevLex }]` | `ArkGrev<W>` parallel |
//! | `[Block { Some(..), GrevLex }, Block { .., GrevLex }]` | `ZippelElimMono<W>` serial (2-block elim) |
//! | `[Block { Some(..), Lex }, Block { .., GrevLex }, …]` | `ZippelTieredElimMono<W>` serial (tiered) |
//!
//! `GrevLex`-then-`Lex` block combos are not supported by ark-gb and are
//! handled by the Singular backend.

use std::marker::PhantomData;

use ark_ff::PrimeField;
use graph::PRef;
use share::Set;

use crate::backend::ark_gb::adapter::{
    TierLayoutGuard, ZippelTieredElimMono, assert_fits_in_ark_gb, build_tier_layout,
    collect_and_validate, compute_gb_pipeline, compute_reduced_gb_grevlex,
    compute_reduced_gb_with_elim, constant_only_basis,
};
use crate::backend::{GbBackend, GbBasis};
use crate::frontend::{BackendError, BlockKind, MonoOrder, Polynomial};

/// ark-gb backend with a configurable packed monomial width `w`.
///
/// Defaults to `w=128` (supports up to 1023 symbolic variables).
/// Use [`with_width`](Self::with_width) for smaller problems.
pub struct ArkGb<F: PrimeField> {
    _phantom: PhantomData<F>,
    w: usize,
}

impl<F: PrimeField> ArkGb<F> {
    pub fn with_width(w: usize) -> Self {
        ArkGb {
            _phantom: PhantomData,
            w,
        }
    }
}

impl<F: PrimeField> Default for ArkGb<F> {
    fn default() -> Self {
        ArkGb {
            _phantom: PhantomData,
            w: 128,
        }
    }
}

impl<F: PrimeField> GbBackend<F> for ArkGb<F> {
    fn compute_gb(
        &self,
        ideal: Vec<Polynomial<F>>,
        order: &MonoOrder,
    ) -> Result<GbBasis<F>, BackendError> {
        let w = self.w;
        let blocks = order.blocks();

        // Case 1: single GrevLex block, vars inferred.
        if blocks.len() == 1
            && blocks[0].vars.is_none()
            && matches!(blocks[0].kind, BlockKind::GrevLex)
        {
            let result = match w {
                8 => compute_reduced_gb_grevlex::<F, 8>(ideal),
                16 => compute_reduced_gb_grevlex::<F, 16>(ideal),
                128 => compute_reduced_gb_grevlex::<F, 128>(ideal),
                _ => panic!("unsupported W={w}"),
            };
            return Ok(GbBasis {
                polys: result,
                order: order.clone(),
            });
        }

        // Case 2: 2-block GrevLex/GrevLex (elim order).
        if blocks.len() == 2
            && matches!(blocks[0].kind, BlockKind::GrevLex)
            && matches!(blocks[1].kind, BlockKind::GrevLex)
        {
            let elim_vars: Set<PRef> = blocks[0]
                .vars
                .as_ref()
                .map(|vs| vs.iter().cloned().collect())
                .unwrap_or_default();
            let eliminate_fn = |v: &PRef| elim_vars.contains(v);
            let result = match w {
                8 => compute_reduced_gb_with_elim::<F, 8>(ideal, &eliminate_fn),
                16 => compute_reduced_gb_with_elim::<F, 16>(ideal, &eliminate_fn),
                128 => compute_reduced_gb_with_elim::<F, 128>(ideal, &eliminate_fn),
                _ => panic!("unsupported W={w}"),
            };
            return Ok(GbBasis {
                polys: result,
                order: order.clone(),
            });
        }

        // Case 3: first block Lex, rest GrevLex (tiered order).
        if matches!(blocks[0].kind, BlockKind::Lex)
            && blocks[1..]
                .iter()
                .all(|b| matches!(b.kind, BlockKind::GrevLex))
        {
            let result = dispatch_tiered(ideal, order, w)?;
            return Ok(GbBasis {
                polys: result,
                order: order.clone(),
            });
        }

        Err(BackendError::UnsupportedOrder)
    }

    fn reduce(&self, p: Polynomial<F>, basis: &GbBasis<F>) -> Polynomial<F> {
        crate::backend::reduce(p, &basis.polys, &basis.order)
    }
}

// -----------------------------------------------------------------------
// Tiered dispatch
// -----------------------------------------------------------------------

fn dispatch_tiered<F: PrimeField>(
    input: Vec<Polynomial<F>>,
    order: &MonoOrder,
    w: usize,
) -> Result<Vec<Polynomial<F>>, BackendError> {
    let (vars, exponents_fit) = collect_and_validate(&input);

    if vars.is_empty() {
        return Ok(constant_only_basis(&input));
    }

    // Build var_order and group_lens from MonoOrder blocks.
    // Deduplicate: a PRef may appear in multiple groups; only its first
    // occurrence counts.
    let mut var_order: Vec<PRef> = Vec::new();
    let mut seen: Set<PRef> = Set::new();
    let mut group_lens: Vec<(usize, usize)> = Vec::new();

    for (i, block) in order.blocks().iter().enumerate() {
        let block_vars: Vec<PRef> = if let Some(vs) = &block.vars {
            vs.iter().filter(|v| !seen.contains(v)).cloned().collect()
        } else {
            // "Remaining vars" block: all vars not yet assigned, sorted by PRef.
            vars.iter().filter(|v| !seen.contains(v)).cloned().collect()
        };

        for v in &block_vars {
            seen.insert(v.clone());
        }

        let len = block_vars.len();
        if len == 0 {
            continue;
        }

        var_order.extend(block_vars);
        group_lens.push((i, len));
    }

    // Any vars not covered by any block go into a final GrevLex block.
    let remaining: Vec<PRef> = vars.iter().filter(|v| !seen.contains(v)).cloned().collect();
    if !remaining.is_empty() {
        let raw_tier = group_lens.len();
        let rem_len = remaining.len();
        var_order.extend(remaining);
        group_lens.push((raw_tier, rem_len));
    }

    let nvars = var_order.len();
    if nvars == 0 {
        return Ok(constant_only_basis(&input));
    }

    match w {
        8 => compute_tiered_with_layout::<F, 8>(input, var_order, group_lens, nvars, exponents_fit),
        16 => {
            compute_tiered_with_layout::<F, 16>(input, var_order, group_lens, nvars, exponents_fit)
        }
        128 => {
            compute_tiered_with_layout::<F, 128>(input, var_order, group_lens, nvars, exponents_fit)
        }
        _ => panic!("unsupported W={w}"),
    }
}

fn compute_tiered_with_layout<F: PrimeField, const W: usize>(
    input: Vec<Polynomial<F>>,
    var_order: Vec<PRef>,
    group_lens: Vec<(usize, usize)>,
    nvars: usize,
    exponents_fit: bool,
) -> Result<Vec<Polynomial<F>>, BackendError> {
    assert_fits_in_ark_gb::<W>(nvars, exponents_fit);

    let layout = build_tier_layout::<W>(&group_lens, nvars);
    let _guard = TierLayoutGuard::<W>::install(layout);

    Ok(compute_gb_pipeline::<F, ZippelTieredElimMono<W>, W, _>(
        input,
        var_order,
        exponents_fit,
        |ring, polys| ark_gb::bba::compute_gb_serial::<F, ZippelTieredElimMono<W>, W>(ring, polys),
    ))
}
