//! Vectors: literals, comprehensions, `reduce` and indexing.

use super::*;
use crate::typ::CTyps;

impl CRef<'_> {
    pub(super) fn infer_vec(self, v: &Exps, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        let ts: CTyps = v
            .iter()
            .map(|e| Spanned::dummy(env.typ(self.at(e))))
            .collect();

        // Vectors cannot be empty for type inference to work
        if ts.is_empty() {
            return Err(TypeError::vec_empty(kctx, vctx));
        }

        // For reference, the type of the first element
        let mut t = ts.0[0].node.clone();

        // Unify types of all elements in the vector to [t]
        for (i, tx) in ts.0.iter().enumerate().skip(1) {
            t = CTyp::lub_equ(&t, tx, kctx).map_err(|e| {
                TypeError::vec(
                    kctx,
                    vctx,
                    self.at(v[i]),
                    tx,
                    self.at(v[0]),
                    &ts.0[0],
                    e.into(),
                )
            })?;
        }

        // Vector length
        let n = ts.len();

        // Generalize the type of the parameters
        Ok(CTyp::vec(&t, n))
    }

    /// The type of the binder `id` of comprehension `[x for id in r]`: an element of the
    /// nonempty vector `r`; checked once `r` is typed, before `x` is.
    pub(super) fn map_elem(
        self,
        x: CRef<'_>,
        id: &Spanned<Vid>,
        r: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        match env.typ(r) {
            CTyp::Vec(inner, n) if n.node > 0 => Ok(inner.node),
            tr => Err(TypeError::map(kctx, vctx, x, &id.node, r, &tr)),
        }
    }

    /// `[x for id in r]`: a vector of `x`s, one per element of `r`.
    pub(super) fn infer_map(self, x: CRef<'_>, r: CRef<'_>, env: &Env<'_>) -> CTyp {
        let CTyp::Vec(_, n) = env.typ(r) else {
            unreachable!("checked by `map_elem`")
        };
        CTyp::vec(&env.typ(x), n.node)
    }

    pub(super) fn infer_reduce(
        self,
        op: BinOp,
        v: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        let tv = env.typ(v);

        match tv {
            CTyp::Vec(elem, n) if n.node > 0 => {
                // Multiplying a vector of polynomials multiplies all factors, so
                // the resulting degree is the element degree times vector length.
                if op == BinOp::Mul
                    && let CTyp::Poly(_, _, d) = &elem.node
                {
                    // Validate the pairwise multiplication under the kind context first.
                    let res_t = CTyp::lub_op(op, &elem, &elem, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                    if let CTyp::Poly(res_a, num_vars, _) = res_t {
                        let degree = d.checked_mul(n.node).ok_or_else(|| {
                            TypeError::lub(
                                TypeError::exp(kctx, vctx, self),
                                LubError::DegreeOverflow(d.node, n.node),
                            )
                        })?;
                        return Ok(CTyp::Poly(res_a, num_vars, Spanned::dummy(degree)));
                    }
                }

                let result = CTyp::lub_op(op, &elem, &elem, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                if result == elem.node {
                    Ok(elem.node.clone())
                } else {
                    Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::ReduceAcc(
                            kctx.clone(),
                            vctx.clone(),
                            op,
                            self.to_expr(),
                            elem.node.clone(),
                            result,
                        ),
                    ))
                }
            }
            _ => Err(TypeError::next(
                TypeError::exp(kctx, vctx, self),
                TypeError::reduce(kctx, vctx, op, v, &tv),
            )),
        }
    }

    pub(super) fn infer_ram(
        self,
        a: CRef<'_>,
        b: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        let ta = env.typ(a);
        let tb = env.typ(b);

        // The index must be a compile-time known integer (Fin type).
        // Fin types arise from literals, ranges, size parameters, and
        // loop variables bound to fixed ranges — all compile-time known.
        // Non-Fin indices (e.g. Scalar-typed runtime values) are rejected
        // because the GB analysis cannot resolve dynamic RAM reads.
        // A strided index `[start, step..end]` reaches `end - step`
        // at most, so it may name an `end` past the vector's length.
        let in_bounds = |r: &crate::typ::CRange, n: usize| {
            r.end() <= n || (!r.is_empty() && r.start() + (r.len() - 1) * r.step() < n)
        };
        match (&ta, &tb) {
            // An integer beyond the finite-index range is never reduced to an index.
            (_, CTyp::FieldLiteral) => Err(TypeError::located(
                b.span(),
                TypeError::FiniteIndexOverflow(kctx.clone(), vctx.clone(), self.to_expr()),
            )),
            (CTyp::Vec(typ, n), CTyp::Fin(r)) => {
                if in_bounds(r, n.node) {
                    Ok(typ.node.clone())
                } else {
                    Err(TypeError::ram(kctx, vctx, self, ta, tb))
                }
            }
            (CTyp::Vec(typ, n), CTyp::Vec(CTyp::Fin(r), m)) => {
                if in_bounds(r, n.node) {
                    Ok(CTyp::vec(&typ.node, m.node))
                } else {
                    Err(TypeError::ram(kctx, vctx, self, ta, tb))
                }
            }
            // Index is not Fin-typed → dynamic RAM, unsupported.
            _ => Err(TypeError::ram_dynamic_index(kctx, vctx, self, ta, tb)),
        }
    }
}
