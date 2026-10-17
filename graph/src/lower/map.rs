//! Persistent `Map`/`ReduceMap` templates for pure loop bodies.

use super::*;
use std::collections::HashMap;

use lang::ast::{ExpId, Exprs, Visit};

impl<C: HasOpFactory> UDag<C> {
    /// Lower a Map/ReduceMap body to an inline `GOp` op-tree (no graph nodes).
    /// `binders` are the enclosing loop binders by de Bruijn level (index =
    /// level); `vctx` is already extended with their CTyps. `Ok(None)` means
    /// the template declines and the caller falls back to the unroll lowerer.
    ///
    /// `CExp::Verify` is intentionally not handled here — the catch-all
    /// `_ => Ok(None)` declines it, forcing the unroll path which creates
    /// top-level `Node::verify` graph nodes (one per element). This ensures
    /// `Op::Verify` never appears nested inside an `Op::Map` or
    /// `Op::ReduceMap` op tree, so `find_verify` (which only inspects
    /// top-level node ops) and the runtime's `check_results` map (keyed by
    /// `NodeIndex`) always find every Verify.
    ///
    /// `expected` is the type the body's value must take, if any: finite-index leaves it
    /// declares field elements are embedded into the field (see [`coerce_field_op`]).
    #[allow(clippy::too_many_arguments)]
    #[stack_guard]
    pub(super) fn lower_loop_body_template(
        &mut self,
        exprs: &mut Arena,
        id: ExpId,
        binders: &[(Vid, ATyp)],
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        expected: Option<&ATyp>,
    ) -> Result<Option<GOp<C>>, GraphError> {
        let op = self
            .lower_loop_body_template_raw(exprs, id, binders, kctx, fctx, vctx, vars, expected)?;
        Ok(match expected {
            Some(target) => op.map(|op| coerce_field_op(op, target, binders.len())),
            None => op,
        })
    }

    /// [`Self::lower_loop_body_template`] before the final coercion to `expected`, which
    /// only steers literals and the elements of vectors, records and map outputs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn lower_loop_body_template_raw(
        &mut self,
        exprs: &mut Arena,
        id: ExpId,
        binders: &[(Vid, ATyp)],
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        expected: Option<&ATyp>,
    ) -> Result<Option<GOp<C>>, GraphError> {
        // The element type the expectation declares for a vector's entries.
        let expected_elem = match expected {
            Some(ATyp::Vec(deref!(elem), _)) => Some(elem),
            _ => None,
        };
        // A subexpression's template, declining (`None`) when it declines.
        macro_rules! sub {
            ($e:expr, $expected:expr) => {
                match self.lower_loop_body_template(
                    exprs, $e, binders, kctx, fctx, vctx, vars, $expected,
                )? {
                    Some(op) => op,
                    None => return Ok(None),
                }
            };
        }
        match exprs[id].clone() {
            CExp::Lit(n) => {
                let typ = exprs.infer(id, kctx, vctx)?;
                let field = expected.is_some_and(ATyp::is_scalar);
                Ok(Some(GOp::Value(literal_value::<C>(&n, &typ, field))))
            }
            CExp::Unit => Ok(Some(GOp::Value(Value::Unit))),
            CExp::Range(r) => Ok(Some(GOp::range(r))),
            CExp::Var(v) => {
                if let Some(level) = binders.iter().rposition(|(b, _)| *b == v.node) {
                    Ok(Some(GOp::loop_param(level, binders[level].1.clone())))
                } else {
                    Ok(Some(Self::op_from_var(&v, vars)?))
                }
            }
            CExp::Bin(op, a, b) => {
                let la = sub!(a, None);
                let lb = sub!(b, None);
                let ctyp = exprs.infer(id, kctx, vctx)?;
                let Some(atyp) = ATyp::from_ctyp(&ctyp, kctx) else {
                    return Ok(None);
                };
                Ok(Some(field_bin(op, la, lb, atyp)))
            }
            CExp::Ram(a, b) => {
                let la = sub!(a, None);
                let lb = sub!(b, None);
                Ok(Some(GOp::ram(la, lb)))
            }
            CExp::Vec(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for e in xs.iter() {
                    out.push(sub!(e, expected_elem));
                }
                Ok(Some(GOp::vec(out)))
            }
            CExp::Evaluate(p, selector, opt_points) => {
                let lp = sub!(p, None);
                match (selector, opt_points) {
                    (None, None) => Ok(Some(GOp::evaluate_grid(lp))),
                    (None, Some(x)) => {
                        let lx = sub!(x, None);
                        Ok(Some(GOp::evaluate(lp, lx)))
                    }
                    (Some(range), Some(fixed)) => {
                        let lfixed = sub!(fixed, None);
                        Ok(Some(GOp::evaluate_selected(lp, range, lfixed)))
                    }
                    (Some(_), None) => Ok(None),
                }
            }
            CExp::Poly(p) => Ok(Some(Op::Poly(mk::<C>(sub!(p, None))))),
            CExp::Coef(p) => Ok(Some(Op::Coef(mk::<C>(sub!(p, None))))),
            CExp::Mle(p) => Ok(Some(Op::Mle(mk::<C>(sub!(p, None))))),
            CExp::Interpolate(points_opt, evals) => {
                let levals = sub!(evals, None);
                match points_opt {
                    None => Ok(Some(Op::Ifft(mk::<C>(levals)))),
                    Some(p) => {
                        let lp = sub!(p, None);
                        Ok(Some(Op::Interpolate(mk::<C>(lp), mk::<C>(levals))))
                    }
                }
            }
            CExp::Proj(r, field) => {
                let lr = sub!(r, None);
                let ctyp = exprs.infer(id, kctx, vctx)?;
                let Some(atyp) = ATyp::from_ctyp(&ctyp, kctx) else {
                    return Ok(None);
                };
                Ok(Some(Op::Proj(mk::<C>(lr), field.node, atyp)))
            }
            CExp::Record(fields) => {
                let mut out: Ctx<String, HOp<C>> = Ctx::new();
                for (k, v) in fields.iter() {
                    let field_target = match expected {
                        Some(ATyp::Record(targets)) => targets.get(&k.node),
                        _ => None,
                    };
                    let lv = sub!(*v, field_target);
                    out.insert(k, &mk::<C>(lv));
                }
                Ok(Some(Op::Record(out)))
            }
            CExp::Map(body, binder, domain) => {
                let domain_typ = exprs.infer(domain, kctx, vctx)?;
                let (elem_ctyp, _) = match domain_typ {
                    CTyp::Vec(deref!(e), n) => (e, n),
                    _ => return Ok(None),
                };
                let Some(binder_atyp) = ATyp::from_ctyp(&elem_ctyp, kctx) else {
                    return Ok(None);
                };
                let ld = sub!(domain, None);
                let mut inner_binders = binders.to_vec();
                inner_binders.push((binder.node.clone(), binder_atyp));
                let mut inner_vctx = vctx.clone();
                inner_vctx.insert(&binder.node, &elem_ctyp);
                let Some(lb) = self.lower_loop_body_template(
                    exprs,
                    body,
                    &inner_binders,
                    kctx,
                    fctx,
                    &inner_vctx,
                    vars,
                    expected_elem,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(GOp::map(ld, lb)))
            }
            CExp::Reduce(rop, v) => {
                if let CExp::Map(body, binder, domain) = exprs[v].clone() {
                    self.try_build_reduce_map(
                        exprs,
                        rop,
                        body,
                        binder.node,
                        domain,
                        binders,
                        kctx,
                        fctx,
                        vctx,
                        vars,
                    )
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    /// Capture-avoiding substitution of `replacement` for free `target` in `exp`, as new
    /// nodes of `exprs`, each spanning the node it rewrites; unchanged subtrees are shared,
    /// not copied. Substitutes through the pure forms that bind nothing (arithmetic,
    /// vectors, polynomials, projections); any other form is kept as is when it does not read
    /// `target`, else the substitution declines (`None`), so composition stays safe.
    pub(super) fn substitute_var(
        exprs: &mut Exprs<BigUint>,
        exp: ExpId,
        target: &Vid,
        replacement: ExpId,
    ) -> Option<ExpId> {
        let substitutes_through = |node: &CExp| {
            matches!(
                node,
                CExp::Var(_)
                    | CExp::Lit(_)
                    | CExp::Unit
                    | CExp::Range(_)
                    | CExp::Bin(..)
                    | CExp::Ram(..)
                    | CExp::Pair(..)
                    | CExp::Vec(_)
                    | CExp::Evaluate(..)
                    | CExp::Poly(_)
                    | CExp::Coef(_)
                    | CExp::Mle(_)
                    | CExp::Interpolate(..)
                    | CExp::Proj(..)
            )
        };
        // The nodes to rebuild, children first. They bind nothing, so `target` is free in
        // every one of them.
        let mut rebuild = Vec::new();
        let mut walk = exprs.at(exp).walk();
        while let Some(visit) = walk.next() {
            match visit {
                Visit::Enter(e) if !substitutes_through(e.node()) => {
                    if e.reads_free(target) {
                        return None;
                    }
                    walk.skip_children();
                }
                Visit::Leave(e) if substitutes_through(e.node()) => rebuild.push(e.id()),
                _ => {}
            }
        }
        let mut new: HashMap<ExpId, ExpId> = HashMap::new();
        for id in rebuild {
            let node = exprs[id].clone();
            if matches!(&node, CExp::Var(x) if x.node == *target) {
                new.insert(id, replacement);
                continue;
            }
            let mut changed = false;
            let node = node.map_ids(|c| match new.get(&c) {
                Some(&n) => {
                    changed = true;
                    n
                }
                None => c,
            });
            if changed {
                let span = exprs.span(id).clone();
                new.insert(id, exprs.push(node, span));
            }
        }
        Some(new.get(&exp).copied().unwrap_or(exp))
    }

    /// Fuse `reduce(rop, [f(x) for x in [g(y) for y in D]])` into a single
    /// reduce-map over `D` with body `f(g(y))`, repeatedly while the inner
    /// comprehension and outer body are pure and substitution is capture-safe.
    /// Returns the maximally composed `(body, binder, domain)` (unchanged when
    /// no safe composition applies).
    pub(super) fn compose_nested_map_domain(
        exprs: &mut Arena,
        mut body: ExpId,
        mut binder: Vid,
        mut domain: ExpId,
    ) -> (ExpId, Vid, ExpId) {
        while let CExp::Map(g, y, d2) = exprs[domain].clone() {
            if !exprs.at(body).is_pure() || !exprs.at(g).is_pure() {
                break;
            }
            let Some(b2) = Self::substitute_var(exprs, body, &binder, g) else {
                break;
            };
            body = b2;
            binder = y.node;
            domain = d2;
        }
        (body, binder, domain)
    }

    /// Build an inline `Op::ReduceMap` for `reduce(rop, [body for binder in
    /// domain])`. Fuses nested-map domains, then lowers domain and body via the
    /// template. Declines (`None`) if any sub-lowering declines.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_build_reduce_map(
        &mut self,
        exprs: &mut Arena,
        rop: BinOp,
        body: ExpId,
        binder: Vid,
        domain: ExpId,
        binders: &[(Vid, ATyp)],
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
    ) -> Result<Option<GOp<C>>, GraphError> {
        let (body, binder, domain) = Self::compose_nested_map_domain(exprs, body, binder, domain);
        let domain_typ = exprs.infer(domain, kctx, vctx)?;
        let (elem_ctyp, _) = match domain_typ {
            CTyp::Vec(deref!(e), n) => (e, n),
            _ => return Ok(None),
        };
        let Some(binder_atyp) = ATyp::from_ctyp(&elem_ctyp, kctx) else {
            return Ok(None);
        };
        let Some(domain_op) =
            self.lower_loop_body_template(exprs, domain, binders, kctx, fctx, vctx, vars, None)?
        else {
            return Ok(None);
        };
        let mut body_binders = binders.to_vec();
        body_binders.push((binder.clone(), binder_atyp));
        let mut body_vctx = vctx.clone();
        body_vctx.insert(&binder, &elem_ctyp);
        let Some(body_op) = self.lower_loop_body_template(
            exprs,
            body,
            &body_binders,
            kctx,
            fctx,
            &body_vctx,
            vars,
            None,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(GOp::reduce_map(rop, domain_op, body_op)))
    }
}
