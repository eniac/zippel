#![allow(refining_impl_trait)]

mod call;
mod error;
mod poly;
mod record;
#[cfg(test)]
mod tests;
mod vector;

pub use error::TypeError;

use std::cell::RefCell;

use num::{BigUint, ToPrimitive};

use crate::ast::range::Range;
use crate::ast::sig::CSig;
use crate::ast::spanned::Spanned;
use crate::ast::{BinOp, CBody, CExp, CExpr, CRef, Exclusion, ExpExclusion, ExpId, Exps, Stmt};
use crate::id::{Tid, Vid};
use crate::stack_guard;
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

/// The types of the nodes of one arena, recorded as inference reaches them, so that inferring a
/// node again, or a new node built over them, does not re-infer their subtrees. Lowering infers
/// every node it lowers; without the table that is quadratic in the nesting depth.
///
/// A node is looked up by id alone, so every inference sharing a table must see each node
/// under the same contexts, as lowering does: a node's scope is fixed by its place in the tree.
#[derive(Debug, Default)]
pub struct TypeTable(RefCell<Vec<Option<CTyp>>>);

impl TypeTable {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn get(&self, id: ExpId) -> Option<CTyp> {
        self.0.borrow().get(id.index()).cloned().flatten()
    }

    fn insert(&self, id: ExpId, typ: &CTyp) {
        let mut types = self.0.borrow_mut();
        if types.len() <= id.index() {
            types.resize(id.index() + 1, None);
        }
        types[id.index()] = Some(typ.clone());
    }
}

/// What inference carries to every node besides the typing contexts.
pub(crate) struct Cx<'a> {
    /// Told the declaration each function call resolves to.
    on_call: &'a dyn Fn(&CSig),
    /// Types already inferred, when the caller keeps them.
    types: Option<&'a TypeTable>,
}

impl Typeable for CRef<'_> {
    type Context = Ctx<Vid, CTyp>;
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        self.infer_in(
            kctx,
            fctx,
            vctx,
            &Cx {
                on_call,
                types: None,
            },
        )
    }
}

impl CRef<'_> {
    /// [`Typeable::infer`], reusing and extending `types`.
    ///
    /// # Errors
    /// Returns the same errors as [`Typeable::infer`].
    pub fn infer_cached(
        self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        types: &TypeTable,
    ) -> Result<CTyp, TypeError> {
        self.infer_in(
            kctx,
            fctx,
            vctx,
            &Cx {
                on_call: &|_| {},
                types: Some(types),
            },
        )
    }

    /// Every node is inferred through here: it guards the stack, which recursion on nested
    /// expressions grows (issue #252), and tags a failure with the span of the innermost
    /// spanned expression on its path.
    #[stack_guard]
    fn infer_in(
        self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        if let Some(typ) = cx.types.and_then(|types| types.get(self.id())) {
            return Ok(typ);
        }
        let typ = self
            .infer_node(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::located(self.span(), e))?;
        if let Some(types) = cx.types {
            types.insert(self.id(), &typ);
        }
        Ok(typ)
    }
}

/// A tree is inferred from its root.
impl Typeable for CExpr {
    type Context = Ctx<Vid, CTyp>;
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        self.root().infer_with_calls(kctx, fctx, vctx, on_call)
    }
}

impl CRef<'_> {
    /// The type of this node, its children inferred under the same contexts.
    fn infer_node(
        self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let at = |id: &ExpId| self.at(*id);
        match self.node() {
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
                self.infer_interpolate(points_opt.as_ref().map(at), at(evals), kctx, fctx, vctx, cx)
            }

            // `poly(v: [F; k])` with `k >= 1` yields `Poly<F, 1, k - 1>`
            // (degree convention: `m = k - 1`).
            CExp::Poly(v) => self.infer_poly(at(v), kctx, fctx, vctx, cx),

            // `coef(p: Poly<F, 1, m>)` yields `[F; m + 1]` (coefficient count
            // is degree + 1 under the Phase 14 degree convention).
            CExp::Coef(p) => self.infer_coef(at(p), kctx, fctx, vctx, cx),

            CExp::Evaluate(p, selector, opt_points) => self.infer_evaluate(
                at(p),
                selector.as_ref(),
                opt_points.as_ref().map(at),
                kctx,
                fctx,
                vctx,
                cx,
            ),

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CExp::Mle(v) => self.infer_mle(at(v), kctx, fctx, vctx, cx),

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CExp::Vec(v) => self.infer_vec(v, kctx, fctx, vctx, cx),

            CExp::Pair(t, e) => self.infer_pair(at(t), at(e), kctx, fctx, vctx, cx),

            CExp::Bin(op, a, b) => self.infer_bin(*op, at(a), at(b), kctx, fctx, vctx, cx),

            // Unary negation: a negated integer is only meaningful in a field; every other
            // operand keeps its type.
            CExp::Neg(a) => self.infer_neg(at(a), kctx, fctx, vctx, cx),

            // Range expression
            CExp::Range(r) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start(), r.step(), r.end())
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(&CTyp::Fin(rr.clone()), rr.len()))
            }

            // Map comprehension
            CExp::Map(x, id, r) => self.infer_map(at(x), id, at(r), kctx, fctx, vctx, cx),

            CExp::Reduce(op, v) => self.infer_reduce(*op, at(v), kctx, fctx, vctx, cx),
            // Variable context lookup
            CExp::Var(id) => vctx
                .get(&id.node)
                .cloned()
                .ok_or(TypeError::var_not_found(&id.node, vctx)),

            // Random oracle challenge
            CExp::Challenge(t, x) | CExp::Random(t, x) => {
                self.infer_sample(t, x.as_ref(), kctx, fctx, vctx, cx)
            }

            // Random access into vectors
            CExp::Ram(a, b) => self.infer_ram(at(a), at(b), kctx, fctx, vctx, cx),

            // Function or polynomial application
            CExp::App(id, params) => self.infer_app(id, params, kctx, fctx, vctx, cx),

            CExp::Verify(exp) => self.infer_verify(at(exp), kctx, fctx, vctx, cx),

            CExp::Block(stmts, tail) => {
                self.infer_block(stmts, tail.as_ref().map(at), kctx, fctx, vctx, cx)
            }

            CExp::Fun(vars, body) => self.infer_fun(vars, at(body), kctx, fctx, vctx, cx),

            CExp::Record(fields) => self.infer_record(fields, kctx, fctx, vctx, cx),

            CExp::Proj(record_exp, field_name) => {
                self.infer_proj(at(record_exp), field_name, kctx, fctx, vctx, cx)
            }

            CExp::SetRecord(record_exp, field_name, value_exp) => self.infer_set_record(
                at(record_exp),
                field_name,
                at(value_exp),
                kctx,
                fctx,
                vctx,
                cx,
            ),
        }
    }
}

/// The match arms of `CRef::infer_node`, one function each (the larger groups live in
/// the `call`, `poly`, `record` and `vector` submodules). Debug builds give every arm's locals
/// their own stack slots, so keeping them out of the dispatcher keeps each level of expression
/// nesting to a small frame (issue #252).
impl CRef<'_> {
    /// Infers a block: each statement in order, with its `let`/`<-` variable bound for the rest
    /// of the block, then the block's value (`()` without one). A failure without a span of its
    /// own is located at its statement.
    #[inline(never)]
    fn infer_block(
        self,
        stmts: &[Spanned<Stmt>],
        tail: Option<CRef<'_>>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let mut vctx = vctx.clone();
        for stmt in stmts {
            let t = self
                .at(stmt.node.value())
                .infer_in(kctx, fctx, &vctx, cx)
                .map_err(|e| TypeError::located(&stmt.span, e))?;
            if let Some(var) = stmt.node.binder() {
                vctx.insert(&var.node, &t);
            }
        }
        tail.map_or(Ok(CTyp::Unit), |tail| tail.infer_in(kctx, fctx, &vctx, cx))
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    fn infer_bin(
        self,
        op: BinOp,
        a: CRef<'_>,
        b: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let ta = a
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;
        let tb = b
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        let t = CTyp::lub_op(op, &ta, &tb, kctx)
            .map_err(|e| TypeError::bin(kctx, vctx, self, &ta, &tb, e))?;

        // Equality is whole-value for every shape, vectors included
        Ok(if op == BinOp::Equ { CTyp::Bool } else { t })
    }

    #[inline(never)]
    fn infer_pair(
        self,
        t: CRef<'_>,
        e: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let ta = t
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;
        let tb = e
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        CTyp::lub_pair(&ta, &tb, kctx)
            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
    }

    #[inline(never)]
    fn infer_neg(
        self,
        a: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let t = a
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;
        Ok(match t {
            CTyp::Fin(_) | CTyp::FieldLiteral => CTyp::FieldLiteral,
            t => t,
        })
    }

    #[inline(never)]
    fn infer_sample(
        self,
        t: &Spanned<Tid>,
        x: Option<&Spanned<ExpExclusion<BigUint>>>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
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
                let v = self.at(*v);
                let tv = v
                    .infer_in(kctx, fctx, vctx, cx)
                    .map_err(|e| TypeError::within(kctx, vctx, self, e))?;
                let of_typ =
                    |elem: &CTyp| CTyp::lub_equ(elem, &typ, kctx).is_ok_and(|elem| elem == typ);
                if !matches!(&tv, CTyp::Vec(elem, _) if of_typ(&elem.node)) {
                    return Err(TypeError::located(
                        v.span(),
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
        self,
        exp: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let t = exp
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        // The operand must be Bool (not Vec<Bool>)
        if t != CTyp::Bool {
            return Err(TypeError::located(
                exp.span(),
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
                        let last = tail(body.root());
                        return Err(TypeError::located(
                            last.span(),
                            TypeError::unit(kctx, vctx, last, &tbody),
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

/// The expression a block ends in, through nested blocks: its value is the block's value.
pub(crate) fn tail(mut e: CRef<'_>) -> CRef<'_> {
    while let CExp::Block(_, Some(value)) = e.node() {
        e = e.at(*value);
    }
    e
}
