//! ark-gb backend: interprets [`MonoOrder`] and routes through the external
//! ark-gb crate.
//!
//! Supported `MonoOrder` patterns (others return [`UnsupportedMonoOrder`]):
//!
//! | Pattern | ark-gb path |
//! |---------|-------------|
//! | `[Block { None, GrevLex }]` | `ArkGrev<W>` parallel |
//! | `[Block { Some(..), GrevLex }, Block { .., GrevLex }]` | `ZippelElimMono<W>` serial (2-block elim) |
//! | `[Block { Some(..), Lex }, Block { .., GrevLex }, …]` | `ZippelTieredElimMono<W>` serial (tiered) |
//!
//! `DegLex`, `WeightedRevLex`, `WeightedLex`, and mixed Lex-after-GrevLex are
//! not supported by ark-gb and reserved for the singular backend.

use std::marker::PhantomData;

use ark_ff::Field;
use backend::{ArkConfig, op::HasOpFactory};
use graph::PRef;
use share::{Ctx, Set};

use crate::backend::ark_gb::adapter::{
    TierLayoutGuard, ZippelTieredElimMono, assert_fits_in_ark_gb, build_tier_layout,
    collect_and_validate, compute_gb_pipeline, compute_reduced_gb_grevlex,
    compute_reduced_gb_with_elim, constant_only_basis,
};
use crate::backend::ark_gb::monomial::{GrevLexTerm, Monomial as OldMonomial};
use crate::backend::ark_gb::sparsepoly::SparsePolynomial;
use crate::frontend::{
    BlockKind, MonoOrder, Monomial as FrontMonomial, Polynomial, UnsupportedMonoOrder,
};

use crate::backend::{GbBackend, GbBasis};

pub struct ArkGb<C: ArkConfig> {
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig> Default for ArkGb<C> {
    fn default() -> Self {
        ArkGb {
            _phantom: PhantomData,
        }
    }
}

// -----------------------------------------------------------------------
// Conversions between order-free Polynomial<F> and old SparsePolynomial<F, T>
// -----------------------------------------------------------------------

fn to_internal_poly<F: Field, T: OldMonomial>(p: Polynomial<F>) -> SparsePolynomial<F, T> {
    let mut terms: Ctx<T, F> = Ctx::new();
    for (mono, coeff) in p.terms {
        let pairs: Vec<(PRef, usize)> = mono.vars().into_iter().zip(mono.powers()).collect();
        let old_term: T = T::from(pairs);
        terms.insert(&old_term, &coeff);
    }
    SparsePolynomial { terms }
}

fn from_internal_poly<F: Field, T: OldMonomial>(p: SparsePolynomial<F, T>) -> Polynomial<F> {
    let mut terms = std::collections::HashMap::new();
    for (old_term, coeff) in p.terms.into_iter() {
        let pairs: Vec<(PRef, usize)> =
            old_term.vars().into_iter().zip(old_term.powers()).collect();
        let mono = FrontMonomial::from(pairs);
        terms.insert(mono, coeff);
    }
    terms.retain(|_, c| !c.is_zero());
    Polynomial { terms }
}

// -----------------------------------------------------------------------
// GbBackend impl
// -----------------------------------------------------------------------

impl<C: ArkConfig + HasOpFactory> GbBackend<C> for ArkGb<C> {
    fn compute_gb(
        &self,
        ideal: Vec<Polynomial<C::F>>,
        order: &MonoOrder,
        w: usize,
    ) -> Result<GbBasis<C::F>, UnsupportedMonoOrder> {
        let blocks = order.blocks();

        // Case 1: single GrevLex block, vars inferred.
        if blocks.len() == 1
            && blocks[0].vars.is_none()
            && matches!(blocks[0].kind, BlockKind::GrevLex)
        {
            let old: Vec<SparsePolynomial<C::F, GrevLexTerm>> =
                ideal.into_iter().map(to_internal_poly).collect();
            let result = match w {
                8 => compute_reduced_gb_grevlex::<C::F, 8>(0, old),
                16 => compute_reduced_gb_grevlex::<C::F, 16>(0, old),
                128 => compute_reduced_gb_grevlex::<C::F, 128>(0, old),
                _ => panic!("unsupported W={w}"),
            };
            return Ok(GbBasis {
                polys: result.into_iter().map(from_internal_poly).collect(),
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
            let old: Vec<SparsePolynomial<C::F, GrevLexTerm>> =
                ideal.into_iter().map(to_internal_poly).collect();
            let result = match w {
                8 => compute_reduced_gb_with_elim::<C::F, GrevLexTerm, 8>(0, old, &eliminate_fn),
                16 => compute_reduced_gb_with_elim::<C::F, GrevLexTerm, 16>(0, old, &eliminate_fn),
                128 => {
                    compute_reduced_gb_with_elim::<C::F, GrevLexTerm, 128>(0, old, &eliminate_fn)
                }
                _ => panic!("unsupported W={w}"),
            };
            return Ok(GbBasis {
                polys: result.into_iter().map(from_internal_poly).collect(),
                order: order.clone(),
            });
        }

        // Case 3: first block Lex, rest GrevLex (tiered order).
        if matches!(blocks[0].kind, BlockKind::Lex)
            && blocks[1..]
                .iter()
                .all(|b| matches!(b.kind, BlockKind::GrevLex))
        {
            let old: Vec<SparsePolynomial<C::F, GrevLexTerm>> =
                ideal.into_iter().map(to_internal_poly).collect();
            let result = dispatch_tiered(old, order, w)?;
            return Ok(GbBasis {
                polys: result.into_iter().map(from_internal_poly).collect(),
                order: order.clone(),
            });
        }

        Err(UnsupportedMonoOrder)
    }

    fn reduce(&self, p: Polynomial<C::F>, basis: &GbBasis<C::F>) -> Polynomial<C::F> {
        use crate::backend::ark_gb::adapter::{LocalRankGuard, get_local_rank};
        use crate::backend::ark_gb::buchberger::GroebnerBasis;
        use crate::backend::ark_gb::tiered::{TieredElimMono, TieredElimStrategy};

        let blocks = basis.order.blocks();
        let is_single_grevlex = blocks.len() == 1
            && blocks[0].vars.is_none()
            && matches!(blocks[0].kind, crate::frontend::BlockKind::GrevLex);

        if is_single_grevlex {
            // GrevLex: use old proven reduce.
            let old_basis: Vec<SparsePolynomial<C::F, GrevLexTerm>> = basis
                .polys
                .iter()
                .map(|p| to_internal_poly(p.clone()))
                .collect();
            let old_gb = GroebnerBasis::new(0, old_basis);
            from_internal_poly(old_gb.reduce(to_internal_poly(p)))
        } else if matches!(blocks[0].kind, crate::frontend::BlockKind::Lex) {
            // Lex/tiered: install a local rank map and use TieredElimMono reduce.
            let var_order: Vec<PRef> = blocks
                .iter()
                .flat_map(|b| b.vars.iter().flatten())
                .cloned()
                .collect();

            let rank_map: std::collections::HashMap<usize, usize> = var_order
                .iter()
                .rev()
                .enumerate()
                .map(|(i, v)| (v.reference.node().index(), i))
                .collect();

            // Strategy: all variables in tier 0 (lex).
            struct LexRank;
            impl TieredElimStrategy for LexRank {
                fn tier(_: &PRef) -> Option<usize> {
                    Some(0)
                }
                fn lex_rank(v: &PRef) -> usize {
                    get_local_rank(v).unwrap()
                }
            }

            let _guard = LocalRankGuard::install(rank_map);
            let old_basis: Vec<SparsePolynomial<C::F, TieredElimMono<LexRank>>> = basis
                .polys
                .iter()
                .map(|p| to_internal_poly(p.clone()))
                .collect();
            let old_gb = GroebnerBasis::new(0, old_basis);
            let old_p = to_internal_poly(p);
            from_internal_poly(old_gb.reduce(old_p))
        } else {
            // Fallback: order-aware reduce (e.g. for 2-block elim).
            crate::backend::reduce(p, &basis.polys, &basis.order)
        }
    }
}

// -----------------------------------------------------------------------
// Tiered dispatch
// -----------------------------------------------------------------------

fn dispatch_tiered<F: Field>(
    input: Vec<SparsePolynomial<F, GrevLexTerm>>,
    order: &MonoOrder,
    w: usize,
) -> Result<Vec<SparsePolynomial<F, GrevLexTerm>>, UnsupportedMonoOrder> {
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
        let raw_tier = i;
        group_lens.push((raw_tier, len));
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

fn compute_tiered_with_layout<F: Field, const W: usize>(
    input: Vec<SparsePolynomial<F, GrevLexTerm>>,
    var_order: Vec<PRef>,
    group_lens: Vec<(usize, usize)>,
    nvars: usize,
    exponents_fit: bool,
) -> Result<Vec<SparsePolynomial<F, GrevLexTerm>>, UnsupportedMonoOrder> {
    assert_fits_in_ark_gb::<W>(nvars, exponents_fit);

    let layout = build_tier_layout::<W>(&group_lens, nvars);
    let _guard = TierLayoutGuard::<W>::install(layout);

    Ok(compute_gb_pipeline::<
        F,
        GrevLexTerm,
        ZippelTieredElimMono<W>,
        W,
        _,
    >(input, var_order, exponents_fit, |ring, polys| {
        ark_gb::bba::compute_gb_serial::<F, ZippelTieredElimMono<W>, W>(ring, polys)
    }))
}
