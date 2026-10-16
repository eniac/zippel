#![allow(refining_impl_trait)]

mod call;
mod error;
mod poly;
mod record;
#[cfg(test)]
mod tests;
mod vector;

pub use error::TypeError;

use num::{BigUint, ToPrimitive};

use crate::ast::range::Range;
use crate::ast::sig::CSig;
use crate::ast::spanned::Spanned;
use crate::ast::{BinOp, CBody, CExp, Exclusion, ExpExclusion};
use crate::id::{Tid, Vid};
use crate::typ::lub::{Lub, LubError};
use crate::typ::{CKind, CTyp};
use share::{Ctx, Set};

/// Kind-directed type inference for concretized AST nodes.
///
/// Implemented for `CExp` and `CBody`, i.e. after `concretize` has replaced symbolic sizes
/// with `usize`. Inference is the last `lang`-level check before DAG lowering, so this is
/// where user-facing type errors are raised; shape violations that survive this point are
/// treated as compiler invariants and panic in `Op::typ()`.
pub trait Typeable {
    /// The variable environment this node is inferred under; `Ctx<Vid, CTyp>` for both
    /// expressions and bodies.
    type Context;
    /// Infers the concrete type of this node under the three contexts that flow together
    /// through the checker: `kctx` (kinds of type variables), `fctx` (visible function
    /// signatures), and `vctx` (types of bound value variables).
    ///
    /// # Errors
    /// Returns a `TypeError` whose variant identifies the offending construct — an unbound
    /// variable or type variable, a function application whose arguments do not match any
    /// signature in `fctx`, an operand whose kind is wrong for the operator, a size or
    /// degree mismatch, or a failed least-upper-bound (`LubError`) when combining branch,
    /// element, or operand types. Each variant carries `kctx`, `vctx`, and the expression so
    /// the full typing judgement can be pretty-printed.
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError> {
        self.infer_with_calls(kctx, fctx, vctx, &|_| {})
    }

    /// Infers a type and reports the original concrete signature selected at each function
    /// call. Polynomial applications do not select a declaration and are not reported.
    ///
    /// # Errors
    /// Returns the same errors as [`Self::infer`].
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError>;
}

/// Recursive calls on spanned children resolve here (auto-deref stops at `Spanned<T>`), so a
/// failure is tagged with the span of the innermost spanned expression on its path.
impl<T: Typeable> Typeable for Spanned<T> {
    type Context = T::Context;
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        self.node
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::located(&self.span, e))
    }
}

/// Type inference for [CExp]
impl Typeable for CExp {
    type Context = Ctx<Vid, CTyp>;
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        match self {
            // A literal that is a valid finite index has the singleton type `Fin<n>`; a larger
            // one is only meaningful in a field, so its full value is kept for lowering.
            CExp::Lit(n) => Ok(match n.to_usize() {
                Some(v) if v.checked_add(1).is_some() => CTyp::fin(Range::singleton(v)),
                _ => CTyp::FieldLiteral,
            }),

            // Unit value
            CExp::Unit => Ok(CTyp::Unit),

            // Unary: FFT-grid interpolation; binary: explicit points + evaluations
            CExp::Interpolate(points_opt, evals) => {
                self.infer_interpolate(points_opt.as_deref(), evals, kctx, fctx, vctx, on_call)
            }

            // `poly(v: [F; k])` with `k >= 1` yields `Poly<F, 1, k - 1>`
            // (degree convention: `m = k - 1`).
            CExp::Poly(v) => self.infer_poly(v, kctx, fctx, vctx, on_call),

            // `coef(p: Poly<F, 1, m>)` yields `[F; m + 1]` (coefficient count
            // is degree + 1 under the Phase 14 degree convention).
            CExp::Coef(p) => self.infer_coef(p, kctx, fctx, vctx, on_call),

            CExp::Evaluate(p, selector, opt_points) => self.infer_evaluate(
                p,
                selector.as_ref(),
                opt_points.as_deref(),
                kctx,
                fctx,
                vctx,
                on_call,
            ),

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CExp::Mle(v) => self.infer_mle(v, kctx, fctx, vctx, on_call),

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CExp::Vec(v) => self.infer_vec(v, kctx, fctx, vctx, on_call),

            CExp::Pair(t, e) => self.infer_pair(t, e, kctx, fctx, vctx, on_call),

            CExp::Bin(op, a, b) => self.infer_bin(*op, a, b, kctx, fctx, vctx, on_call),

            // Unary negation: a negated integer is only meaningful in a field; every other
            // operand keeps its type.
            CExp::Neg(a) => self.infer_neg(a, kctx, fctx, vctx, on_call),

            // Range expression
            CExp::Range(r) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start(), r.step(), r.end())
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(&CTyp::Fin(rr.clone()), rr.len()))
            }

            // Map comprehension
            CExp::Map(x, id, r) => self.infer_map(x, id, r, kctx, fctx, vctx, on_call),

            CExp::Reduce(op, v) => self.infer_reduce(*op, v, kctx, fctx, vctx, on_call),
            // Variable context lookup
            CExp::Var(id) => vctx
                .get(&id.node)
                .cloned()
                .ok_or(TypeError::var_not_found(&id.node, vctx)),

            // Random oracle challenge
            CExp::Challenge(t, x) | CExp::Random(t, x) => {
                self.infer_sample(t, x.as_ref(), kctx, fctx, vctx, on_call)
            }

            // Random access into vectors
            CExp::Ram(a, b) => self.infer_ram(a, b, kctx, fctx, vctx, on_call),

            // Function or polynomial application
            CExp::App(id, params) => self.infer_app(id, params, kctx, fctx, vctx, on_call),

            CExp::Verify(exp) => self.infer_verify(exp, kctx, fctx, vctx, on_call),

            CExp::Let(..) | CExp::Log(..) => self.infer_chain(kctx, fctx, vctx, on_call),

            CExp::Fun(vars, body) => self.infer_fun(vars, body, kctx, fctx, vctx, on_call),

            CExp::Record(fields) => self.infer_record(fields, kctx, fctx, vctx, on_call),

            CExp::Proj(record_exp, field_name) => {
                self.infer_proj(record_exp, field_name, kctx, fctx, vctx, on_call)
            }

            CExp::SetRecord(record_exp, field_name, value_exp) => {
                self.infer_set_record(record_exp, field_name, value_exp, kctx, fctx, vctx, on_call)
            }
        }
    }
}

/// The match arms of [`CExp::infer_with_calls`], one function each (the larger groups live in
/// the `call`, `poly`, `record` and `vector` submodules). Debug builds give every arm's locals
/// their own stack slots, so keeping them out of the dispatcher keeps each level of expression
/// nesting to a small frame (issue #252).
impl CExp {
    /// Infers a `let`/`<-`/`;` chain in a loop, so stack depth does not grow with its length.
    /// A failure is located as the `Spanned` wrapper of each chain node would locate it, at the
    /// innermost non-empty span among the nodes below `self` (the caller's wrapper adds `self`'s).
    #[inline(never)]
    fn infer_chain(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        let mut vctx = vctx.clone();
        let mut span = 0..0;
        let mut exp = self;
        loop {
            let (var, left, right) = match exp {
                CExp::Let(var, left, right) => (var.as_ref(), left, right),
                CExp::Log(var, left, right) => (Some(var), left, right),
                // The chain's tail: its value is the chain's value.
                _ => {
                    return exp
                        .infer_with_calls(kctx, fctx, &vctx, on_call)
                        .map_err(|e| TypeError::located(&span, e));
                }
            };
            let tleft = left
                .infer_with_calls(kctx, fctx, &vctx, on_call)
                .map_err(|e| TypeError::located(&span, e))?;
            if let Some(var) = var {
                vctx.insert(&var.node, &tleft);
            }
            let Some(right) = right else {
                return Ok(CTyp::Unit);
            };
            if !right.span.is_empty() {
                span = right.span.clone();
            }
            exp = &right.node;
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    fn infer_bin(
        &self,
        op: BinOp,
        a: &Spanned<CExp>,
        b: &Spanned<CExp>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        let ta = a
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
        let tb = b
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

        let t = CTyp::lub_op(op, &ta, &tb, kctx)
            .map_err(|e| TypeError::bin(kctx, vctx, self, &ta, &tb, e))?;

        // Equality is whole-value for every shape, vectors included
        Ok(if op == BinOp::Equ { CTyp::Bool } else { t })
    }

    #[inline(never)]
    fn infer_pair(
        &self,
        t: &Spanned<CExp>,
        e: &Spanned<CExp>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        let ta = t
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
        let tb = e
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

        CTyp::lub_pair(&ta, &tb, kctx)
            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
    }

    #[inline(never)]
    fn infer_neg(
        &self,
        a: &Spanned<CExp>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        let t = a
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
        Ok(match t {
            CTyp::Fin(_) | CTyp::FieldLiteral => CTyp::FieldLiteral,
            t => t,
        })
    }

    #[inline(never)]
    fn infer_sample(
        &self,
        t: &Spanned<Tid>,
        x: Option<&Spanned<ExpExclusion<BigUint>>>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        // What kind of [t]?
        let k = kctx.get(&t.node).ok_or(TypeError::lub(
            TypeError::exp(kctx, vctx, self),
            LubError::kind_not_found(&t.node),
        ))?;

        if !k.is_scalar() {
            return Err(TypeError::challenge(kctx, vctx, &t.node, k));
        }

        let typ = CTyp::base(&t.node);
        match x.as_ref().map(|x| (&x.node, &x.span)) {
            // `x^0 == 1` for every `x`: nothing would be left to sample.
            Some((Exclusion::RootsOfUnity(n), span)) if n.node == 0 => {
                return Err(TypeError::located(
                    span,
                    TypeError::excludes_all(kctx, vctx, &t.node),
                ));
            }
            // A vector of `t` values.
            Some((Exclusion::Values(v), _)) => {
                let tv = v
                    .infer_with_calls(kctx, fctx, vctx, on_call)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let of_typ =
                    |elem: &CTyp| CTyp::lub_equ(elem, &typ, kctx).is_ok_and(|elem| elem == typ);
                if !matches!(&tv, CTyp::Vec(elem, _) if of_typ(&elem.node)) {
                    return Err(TypeError::located(
                        &v.span,
                        TypeError::exclusion_type(kctx, vctx, &t.node, &tv),
                    ));
                }
            }
            None | Some((Exclusion::RootsOfUnity(_), _)) => {}
        }
        Ok(typ)
    }

    #[inline(never)]
    fn infer_verify(
        &self,
        exp: &Spanned<CExp>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        let t = exp
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

        // The operand must be Bool (not Vec<Bool>)
        if t != CTyp::Bool {
            return Err(TypeError::located(
                &exp.span,
                TypeError::condition(kctx, vctx, self, &t),
            ));
        }

        // Assert/Verify return Unit
        Ok(CTyp::Unit)
    }
}

/// Type inference for [CBody]
impl Typeable for CBody {
    type Context = Ctx<Vid, CTyp>;
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        // Type inference for each statement in the Body
        match self {
            CBody::Proto { relation, body } => {
                // Infer the relation (Let/Assert chain — infers to Unit)
                relation.infer_with_calls(kctx, fctx, &vctx.clone(), on_call)?;

                // Then the body (empty body is Unit)
                if let Some(body) = body {
                    let tbody = body.infer_with_calls(kctx, fctx, &vctx.clone(), on_call)?;
                    if tbody != CTyp::Unit {
                        return Err(TypeError::located(
                            &tail(body).span,
                            TypeError::unit(kctx, vctx, tail(body), &tbody),
                        ));
                    }
                }

                Ok(CTyp::Unit)
            }
            CBody::Func { body } => match body {
                Some(body) => body.infer_with_calls(kctx, fctx, &vctx.clone(), on_call),
                None => Ok(CTyp::Unit),
            },
            CBody::TypeAlias => Ok(CTyp::Unit), // Type aliases have no body to check
        }
    }
}

/// The expression a `let`/`<-`/`;` chain ends in: its value is the chain's value.
pub(crate) fn tail(mut e: &Spanned<CExp>) -> &Spanned<CExp> {
    while let CExp::Let(_, _, Some(rest)) | CExp::Log(_, _, Some(rest)) = &e.node {
        e = rest;
    }
    e
}
