#![allow(refining_impl_trait)]

mod call;
mod error;
mod poly;
mod record;
#[cfg(test)]
mod tests;
mod vector;

pub use error::{Sampler, TypeError};

use num::{BigUint, ToPrimitive};
use std::collections::HashMap;

use crate::typ::instantiate::Instantiation;

use crate::ast::range::Range;
use crate::ast::sig::CSig;
use crate::ast::spanned::Spanned;
use crate::ast::{BinOp, Bound, CExp, CExpr, CRef, Exclusion, ExpExclusion, ExpId, Exps, Visit};
use crate::id::{Tid, Vid};
use crate::typ::lub::{Lub, LubError};
use crate::typ::{CKind, CTyp};
use share::{Ctx, ScopedCtx, Set};

/// The result of resolving an ordinary function call during inference.
#[derive(Debug, Clone)]
pub struct ResolvedCall {
    /// The original declaration, used to find its body.
    pub declaration: CSig,
    /// Its signature with type parameters instantiated in the caller's scope.
    pub signature: CSig,
    /// The same substitution, used to instantiate its body.
    pub instantiation: Instantiation,
}

/// The types of the nodes of one arena, indexed by node, filled as inference leaves each node.
/// Inferring a node again, or a new node built over typed ones, then reads its children's types
/// rather than walking their subtrees; lowering infers every node it lowers, so without the
/// table it would be quadratic in the nesting depth.
///
/// A node is looked up by id alone, so every inference sharing a table must see each node
/// under the same contexts, as lowering does: a node's scope is fixed by its place in the tree.
#[derive(Debug, Default, Clone)]
pub struct TypeTable {
    types: Vec<Option<CTyp>>,
    /// Resolved calls in typing order, with an index for lowering.
    calls: Vec<(ExpId, ResolvedCall)>,
    call_indices: HashMap<ExpId, usize>,
}

impl TypeTable {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The call nodes and their resolutions, in typing order.
    pub fn calls(&self) -> &[(ExpId, ResolvedCall)] {
        &self.calls
    }

    /// The resolution of an ordinary function call. Polynomial applications have no record.
    pub fn call(&self, id: ExpId) -> Option<&ResolvedCall> {
        self.call_indices
            .get(&id)
            .map(|&index| &self.calls[index].1)
    }

    fn get(&self, id: ExpId) -> Option<&CTyp> {
        self.types.get(id.index()).and_then(Option::as_ref)
    }

    fn insert(&mut self, id: ExpId, typ: CTyp) {
        if self.types.len() <= id.index() {
            self.types.resize(id.index() + 1, None);
        }
        self.types[id.index()] = Some(typ);
    }
}

/// The contexts a tree is typed under.
#[derive(Clone, Copy)]
pub struct Cx<'a> {
    /// Kinds of the type variables in scope.
    pub kctx: &'a Ctx<Tid, CKind>,
    /// Visible function signatures.
    pub fctx: &'a Set<CSig>,
}

/// The types of the variables in scope. Inference binds into it and undoes its bindings
/// when it leaves their scope, so callers lend their environment instead of copying it.
pub type VarTypes = ScopedCtx<Vid, CTyp>;

/// What a typing rule sees: the contexts at its node, and the types of the nodes already left,
/// its children among them.
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    cx: Cx<'a>,
    vctx: &'a VarTypes,
    types: &'a TypeTable,
}

impl Env<'_> {
    /// The type of `e`, a child of the node being typed.
    fn typ(&self, e: CRef<'_>) -> CTyp {
        self.types
            .get(e.id())
            .cloned()
            .expect("children are typed first")
    }
}

/// A tree is typed from its root, with a table of its own.
impl CExpr {
    /// The type of the tree under the contexts `kctx` (kinds of type variables), `fctx`
    /// (visible function signatures) and `vctx` (types of variables).
    ///
    /// # Errors
    /// The first `TypeError` the tree raises: an unbound variable or type variable, a call no
    /// signature in `fctx` accepts, an operand of the wrong kind, a size or degree mismatch,
    /// or a failed least upper bound of branch, element or operand types.
    pub fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
    ) -> Result<CTyp, TypeError> {
        self.root().infer(
            &Cx { kctx, fctx },
            &mut VarTypes::new(vctx.clone()),
            &mut TypeTable::new(),
        )
    }
}

impl CRef<'_> {
    /// Types the tree under this node in one walk, recording every node's type in `types`.
    /// Each node is typed when the walk leaves it, from its children's types; nodes already in
    /// `types` are not walked again. A binder's type is known when the walk binds it: a
    /// statement's from its value, a comprehension's from its domain, a `fun`'s parameters
    /// from the field in scope. Each node is checked once, when it is left, including its own
    /// annotations (a sample's type, a `.set`'s field), so the error reported is the first
    /// failing check in evaluation order: children before their node, left to right.
    ///
    /// `vctx` holds the variables in scope at this node. It is left as it was, also on error.
    ///
    /// # Errors
    /// As [`CExpr::infer`].
    pub fn infer(
        self,
        cx: &Cx<'_>,
        vctx: &mut VarTypes,
        types: &mut TypeTable,
    ) -> Result<CTyp, TypeError> {
        let outside = vctx.mark();
        let typed = self.infer_in(cx, vctx, types);
        vctx.rollback(outside);
        typed
    }

    /// [`Self::infer`], leaving the variables still in scope on error in `vctx`.
    fn infer_in(
        self,
        cx: &Cx<'_>,
        vctx: &mut VarTypes,
        types: &mut TypeTable,
    ) -> Result<CTyp, TypeError> {
        // Expression and statement locations, innermost last, for diagnostic fallbacks.
        let mut locations = Vec::new();
        let mut walk = self.walk();
        // The environment of a rule, at the variables in scope now.
        macro_rules! env {
            () => {
                Env {
                    cx: *cx,
                    vctx: &*vctx,
                    types: &*types,
                }
            };
        }
        while let Some(visit) = walk.next() {
            match visit {
                Visit::EnterStmt(stmt) => locations.push(&stmt.span),
                Visit::LeaveStmt(_) => {
                    locations.pop();
                }
                Visit::Enter(e) => {
                    locations.push(e.span());
                    if let Some(cached) = types.get(e.id()) {
                        // A node's type is reused by id, which is sound only while the node keeps
                        // its bindings. Lowering infers every variable it lowers, so a node moved
                        // under a binder that captures one of its variables shows up here.
                        debug_assert!(
                            !matches!(e.node(), CExp::Var(x) if vctx.get(&x.node) != Some(cached)),
                            "stale type for `{:?}`: a typed node was moved under another binding",
                            e.node()
                        );
                        walk.skip_children();
                    }
                }
                Visit::Bind(x, bound) => match Self::bound_typ(bound, &env!()) {
                    Ok(t) => vctx.insert(&x.node, &t),
                    Err(err) => return Err(Self::locate(err, &locations)),
                },
                // Bindings end innermost first, so the latest one ends.
                Visit::Unbind(_) => vctx.rollback(vctx.mark() - 1),
                Visit::Leave(e) => {
                    if types.get(e.id()).is_none() {
                        let mut call = None;
                        let typed = e.infer_node(&env!(), &mut call);
                        if let Some(sig) = call {
                            types.call_indices.insert(e.id(), types.calls.len());
                            types.calls.push((e.id(), sig));
                        }
                        match typed {
                            Ok(t) => types.insert(e.id(), t),
                            Err(err) => return Err(Self::locate(err, &locations)),
                        }
                    }
                    locations.pop();
                }
            }
        }
        Ok(types.get(self.id()).cloned().expect("the root is typed"))
    }

    /// `err`, raised at the innermost location, located there or else at the nearest
    /// enclosing node with a span (a statement, then its block, ...).
    fn locate(mut err: TypeError, locations: &[&std::ops::Range<usize>]) -> TypeError {
        for span in locations.iter().rev() {
            if err.span().is_some() {
                break;
            }
            err = TypeError::located(span, err);
        }
        err
    }

    /// The type of a variable bound as `bound`. What it is bound to is typed already: a
    /// statement's value or a comprehension's domain is left before its variable is bound.
    fn bound_typ(bound: Bound<'_, BigUint>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        match bound {
            Bound::Value(value) => Ok(env.typ(value)),
            Bound::Element { map, domain } => map.map_elem(domain, env),
            Bound::Param(fun) => {
                let CExp::Fun(vars, _) = fun.node() else {
                    unreachable!("parameters are bound by a `fun`")
                };
                let field = fun.fun_field(env)?;
                Ok(if vars.len() == 1 {
                    // Univariate: degree 1; the body's degree follows from the lub rules.
                    CTyp::uni(&field, 1)
                } else {
                    CTyp::Base(field)
                })
            }
        }
    }
}

impl CRef<'_> {
    /// The type of this node, from its children's types.
    fn infer_node(self, env: &Env<'_>, call: &mut Option<ResolvedCall>) -> Result<CTyp, TypeError> {
        let vctx = env.vctx;
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
                self.infer_interpolate(points_opt.as_ref().map(at), at(evals), env)
            }

            // `poly(v: [F; k])` with `k >= 1` yields `Poly<F, 1, k - 1>`
            // (degree convention: `m = k - 1`).
            CExp::Poly(v) => self.infer_poly(at(v), env),

            // `coef(p: Poly<F, 1, m>)` yields `[F; m + 1]` (coefficient count
            // is degree + 1 under the Phase 14 degree convention).
            CExp::Coef(p) => self.infer_coef(at(p), env),

            CExp::Evaluate(p, selector, opt_points) => {
                self.infer_evaluate(at(p), selector.as_ref(), opt_points.as_ref().map(at), env)
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CExp::Mle(v) => self.infer_mle(at(v), env),

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CExp::Vec(v) => self.infer_vec(v, env),

            CExp::Pair(t, e) => self.infer_pair(at(t), at(e), env),

            CExp::Bin(op, a, b) => self.infer_bin(*op, at(a), at(b), env),

            // Unary negation: a negated integer is only meaningful in a field; every other
            // operand keeps its type.
            CExp::Neg(a) => self.infer_neg(at(a), env),

            // Range expression
            CExp::Range(r) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start(), r.step(), r.end())
                    .map_err(|e| TypeError::Range(r.clone(), e))?;

                Ok(CTyp::vec(&CTyp::Fin(rr.clone()), rr.len()))
            }

            // Map comprehension
            CExp::Map(x, _, r) => Ok(self.infer_map(at(x), at(r), env)),

            CExp::Reduce(op, v) => self.infer_reduce(*op, at(v), env),
            // Variable context lookup
            CExp::Var(id) => vctx
                .get(&id.node)
                .cloned()
                .ok_or(TypeError::VarNotFound(id.node.clone())),

            // Random oracle challenge
            CExp::Challenge(t, x) | CExp::Random(t, x) => self.infer_sample(t, x.as_ref(), env),

            // Random access into vectors
            CExp::Ram(a, b) => self.infer_ram(at(a), at(b), env),

            // Function or polynomial application
            CExp::App(id, params) => self.infer_app(id, params, env, call),

            CExp::Verify(exp) => self.infer_verify(at(exp), env),

            // A block has its value's type, `()` without one.
            CExp::Block(block) => Ok(block.tail.map_or(CTyp::Unit, |tail| env.typ(at(&tail)))),

            CExp::Fun(vars, body) => self.infer_fun(vars, at(body), env),

            CExp::Record(fields) => self.infer_record(fields, env),

            CExp::Proj(record_exp, field_name) => self.infer_proj(at(record_exp), field_name, env),

            CExp::SetRecord(record_exp, field_name, value_exp) => {
                self.infer_set_record(at(record_exp), field_name, at(value_exp), env)
            }
        }
    }
}

/// The typing rules of `CRef::infer_node`, one function each; the larger groups live in the
/// `call`, `poly`, `record` and `vector` submodules.
impl CRef<'_> {
    fn infer_bin(
        self,
        op: BinOp,
        a: CRef<'_>,
        b: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Cx { kctx, .. } = env.cx;
        let (ta, tb) = (env.typ(a), env.typ(b));
        let t = CTyp::lub_op(op, &ta, &tb, kctx).map_err(|_| {
            TypeError::Bin(
                kctx.clone(),
                op,
                Spanned::new(ta.clone(), a.span().clone()),
                Spanned::new(tb.clone(), b.span().clone()),
            )
        })?;

        // Equality is whole-value for every shape, vectors included
        Ok(if op == BinOp::Equ { CTyp::Bool } else { t })
    }

    fn infer_pair(self, t: CRef<'_>, e: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Cx { kctx, .. } = env.cx;
        CTyp::lub_pair(&env.typ(t), &env.typ(e), kctx).map_err(TypeError::from)
    }

    fn infer_neg(self, a: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        Ok(match env.typ(a) {
            CTyp::Fin(_) | CTyp::FieldLiteral => CTyp::FieldLiteral,
            t => t,
        })
    }

    /// The type a sample of `t` has; checked before what it excludes is typed.
    fn sample_typ(
        self,
        t: &Spanned<Tid>,
        x: Option<&Spanned<ExpExclusion<BigUint>>>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Cx { kctx, .. } = env.cx;
        // What kind of [t]?
        let k = kctx
            .get(&t.node)
            .ok_or(TypeError::from(LubError::kind_not_found(&t.node)))?;
        if !k.is_scalar() {
            let sampler = match self.node() {
                CExp::Random(..) => Sampler::Random,
                _ => Sampler::Challenge,
            };
            return Err(TypeError::Sample(sampler, t.node.clone(), k.clone()));
        }
        // `x^0 == 1` for every `x`: nothing would be left to sample.
        if let Some(x) = x
            && let Exclusion::RootsOfUnity(n) = &x.node
            && n.node == 0
        {
            return Err(TypeError::located(
                &x.span,
                TypeError::ExcludesAll(t.node.clone()),
            ));
        }
        Ok(CTyp::base(&t.node))
    }

    fn infer_sample(
        self,
        t: &Spanned<Tid>,
        x: Option<&Spanned<ExpExclusion<BigUint>>>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Cx { kctx, .. } = env.cx;
        let typ = self.sample_typ(t, x, env)?;
        // What it excludes: a vector of `t` values.
        if let Some(Exclusion::Values(v)) = x.map(|x| &x.node) {
            let v = self.at(*v);
            let tv = env.typ(v);
            let of_typ =
                |elem: &CTyp| CTyp::lub_equ(elem, &typ, kctx).is_ok_and(|elem| elem == typ);
            if !matches!(&tv, CTyp::Vec(elem, _) if of_typ(&elem.node)) {
                return Err(TypeError::located(
                    v.span(),
                    TypeError::ExclusionType(kctx.clone(), t.node.clone(), tv.clone()),
                ));
            }
        }
        Ok(typ)
    }

    fn infer_verify(self, exp: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Cx { kctx, .. } = env.cx;
        let t = env.typ(exp);
        // The operand must be Bool (not Vec<Bool>)
        if t != CTyp::Bool {
            return Err(TypeError::located(
                exp.span(),
                TypeError::Condition(kctx.clone(), t.clone()),
            ));
        }
        Ok(CTyp::Unit)
    }
}

/// The expression a block ends in, through nested blocks: its value is the block's value.
pub(crate) fn tail(mut e: CRef<'_>) -> CRef<'_> {
    while let CExp::Block(crate::ast::Block {
        tail: Some(value), ..
    }) = e.node()
    {
        e = e.at(*value);
    }
    e
}
