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
use crate::ast::{BinOp, CBody, CExp, CExpr, CRef, Exclusion, ExpExclusion, ExpId, Exps, Visit};
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

/// The types of the nodes of one arena, indexed by node, filled as inference leaves each node.
/// Inferring a node again, or a new node built over typed ones, then reads its children's types
/// rather than walking their subtrees; lowering infers every node it lowers, so without the
/// table it would be quadratic in the nesting depth.
///
/// A node is looked up by id alone, so every inference sharing a table must see each node
/// under the same contexts, as lowering does: a node's scope is fixed by its place in the tree.
#[derive(Debug, Default)]
pub struct TypeTable(Vec<Option<CTyp>>);

impl TypeTable {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn get(&self, id: ExpId) -> Option<&CTyp> {
        self.0.get(id.index()).and_then(Option::as_ref)
    }

    fn insert(&mut self, id: ExpId, typ: CTyp) {
        if self.0.len() <= id.index() {
            self.0.resize(id.index() + 1, None);
        }
        self.0[id.index()] = Some(typ);
    }
}

/// What a typing rule sees: the contexts at its node, and the types of the nodes already left,
/// its children among them.
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    kctx: &'a Ctx<Tid, CKind>,
    fctx: &'a Set<CSig>,
    vctx: &'a Ctx<Vid, CTyp>,
    types: &'a TypeTable,
    /// Told the declaration each function call resolves to.
    on_call: &'a dyn Fn(&CSig),
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

impl Typeable for CRef<'_> {
    type Context = Ctx<Vid, CTyp>;
    fn infer_with_calls(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        self.infer_in(kctx, fctx, vctx, on_call, &mut TypeTable::new())
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
    /// [`Typeable::infer`], reusing and extending `types`.
    ///
    /// # Errors
    /// Returns the same errors as [`Typeable::infer`].
    pub fn infer_cached(
        self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        types: &mut TypeTable,
    ) -> Result<CTyp, TypeError> {
        self.infer_in(kctx, fctx, vctx, &|_| {}, types)
    }

    /// Types the tree under this node in one walk, recording every node's type in `types`.
    /// Each node is typed when the walk leaves it, from its children's types; nodes already in
    /// `types` are not walked again. A binder's type is known when the walk binds it: a
    /// statement's from its value, a comprehension's from its domain, a `fun`'s parameters
    /// from the field in scope. Some rules check a node before its children are typed, or
    /// between them (see [`Self::enter`] and [`Self::after_child`]), as a recursive checker
    /// would, so the first error reported is the same.
    pub(crate) fn infer_in(
        self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
        types: &mut TypeTable,
    ) -> Result<CTyp, TypeError> {
        let mut vctx = vctx.clone();
        // The nodes entered and not yet left, each with the variable context to restore when
        // it is left, if it binds variables.
        let mut open: Vec<(CRef<'_>, Option<Ctx<Vid, CTyp>>)> = Vec::new();
        // The node left last: a binder takes its type from it.
        let mut last = self;
        let mut walk = self.walk();
        // The environment of a rule, at variable context `$vctx`.
        macro_rules! env {
            ($vctx:expr) => {
                Env {
                    kctx,
                    fctx,
                    vctx: $vctx,
                    types: &*types,
                    on_call,
                }
            };
        }
        while let Some(visit) = walk.next() {
            match visit {
                Visit::Enter(e) => {
                    let binds = matches!(e.node(), CExp::Block(..) | CExp::Map(..) | CExp::Fun(..));
                    open.push((e, binds.then(|| vctx.clone())));
                    if types.get(e.id()).is_some() {
                        walk.skip_children();
                    } else if let Err(err) = e.enter(&env!(&vctx)) {
                        return Err(Self::locate(err, &open, &vctx, kctx));
                    }
                }
                Visit::Bind(x) => {
                    let (binder, _) = open.last().expect("a binder is open");
                    let t = binder.bind(last, &env!(&vctx));
                    vctx.insert(&x.node, &t);
                }
                Visit::Leave(e) => {
                    if let Some(outer) = open.last_mut().and_then(|(_, saved)| saved.take()) {
                        vctx = outer;
                    }
                    if types.get(e.id()).is_none() {
                        let typed = e.infer_node(&env!(&vctx));
                        match typed {
                            Ok(t) => types.insert(e.id(), t),
                            Err(err) => return Err(Self::locate(err, &open, &vctx, kctx)),
                        }
                    }
                    open.pop();
                    last = e;
                    if let Some((parent, _)) = open.last()
                        && let Err(err) = parent.after_child(e, &env!(&vctx))
                    {
                        return Err(Self::locate(err, &open, &vctx, kctx));
                    }
                }
            }
        }
        Ok(types.get(self.id()).cloned().expect("the root is typed"))
    }

    /// `err`, raised typing the innermost node of `open`, located there, or else at the nearest
    /// enclosing statement or node with a span, with the enclosing node attached.
    fn locate(
        err: TypeError,
        open: &[(CRef<'_>, Option<Ctx<Vid, CTyp>>)],
        vctx: &Ctx<Vid, CTyp>,
        kctx: &Ctx<Tid, CKind>,
    ) -> TypeError {
        let (failed, _) = open.last().expect("the failing node is open");
        let mut err = TypeError::located(failed.span(), err);
        let mut child = *failed;
        for (node, _) in open.iter().rev().skip(1) {
            if child.id() == failed.id() {
                err = TypeError::within(kctx, vctx, *node, err);
            }
            if let CExp::Block(stmts, _) = node.node()
                && let Some(stmt) = stmts.iter().find(|s| s.node.value() == child.id())
            {
                err = TypeError::located(&stmt.span, err);
            }
            err = TypeError::located(node.span(), err);
            if err.span().is_some() {
                break;
            }
            child = *node;
        }
        err
    }

    /// Checks made on entering this node, before any child is typed.
    fn enter(self, env: &Env<'_>) -> Result<(), TypeError> {
        match self.node() {
            CExp::Challenge(t, x) | CExp::Random(t, x) => {
                self.sample_typ(t, x.as_ref(), env).map(drop)
            }
            CExp::Fun(..) => self.fun_field(env).map(drop),
            _ => Ok(()),
        }
    }

    /// Checks made when `child`, a child of this node, has been typed, before the next one is.
    fn after_child(self, child: CRef<'_>, env: &Env<'_>) -> Result<(), TypeError> {
        match self.node() {
            CExp::Map(body, id, domain) if *domain == child.id() => {
                self.map_elem(self.at(*body), id, child, env).map(drop)
            }
            CExp::SetRecord(record, field, _) if *record == child.id() => {
                self.record_field(child, field, env).map(drop)
            }
            _ => Ok(()),
        }
    }

    /// The type of a variable this node binds, `last` being the node the walk left last: a
    /// statement's value, a comprehension's domain.
    fn bind(self, last: CRef<'_>, env: &Env<'_>) -> CTyp {
        match self.node() {
            CExp::Map(body, id, _) => self
                .map_elem(self.at(*body), id, last, env)
                .expect("checked after the domain"),
            CExp::Fun(vars, _) => {
                let field = self.fun_field(env).expect("checked on entry");
                if vars.len() == 1 {
                    // Univariate: degree 1; the body's degree follows from the lub rules.
                    CTyp::uni(&field, 1)
                } else {
                    CTyp::Base(field)
                }
            }
            _ => env.typ(last),
        }
    }
}

impl CRef<'_> {
    /// The type of this node, from its children's types.
    fn infer_node(self, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
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
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(&CTyp::Fin(rr.clone()), rr.len()))
            }

            // Map comprehension
            CExp::Map(x, _, r) => Ok(self.infer_map(at(x), at(r), env)),

            CExp::Reduce(op, v) => self.infer_reduce(*op, at(v), env),
            // Variable context lookup
            CExp::Var(id) => vctx
                .get(&id.node)
                .cloned()
                .ok_or(TypeError::var_not_found(&id.node, vctx)),

            // Random oracle challenge
            CExp::Challenge(t, x) | CExp::Random(t, x) => self.infer_sample(t, x.as_ref(), env),

            // Random access into vectors
            CExp::Ram(a, b) => self.infer_ram(at(a), at(b), env),

            // Function or polynomial application
            CExp::App(id, params) => self.infer_app(id, params, env),

            CExp::Verify(exp) => self.infer_verify(at(exp), env),

            CExp::Block(_, tail) => self.infer_block(tail.as_ref().map(at), env),

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
    /// A block's type: its value's (`()` without one).
    fn infer_block(self, tail: Option<CRef<'_>>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        Ok(tail.map_or(CTyp::Unit, |tail| env.typ(tail)))
    }

    fn infer_bin(
        self,
        op: BinOp,
        a: CRef<'_>,
        b: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        let (ta, tb) = (env.typ(a), env.typ(b));
        let t = CTyp::lub_op(op, &ta, &tb, kctx)
            .map_err(|e| TypeError::bin(kctx, vctx, self, &ta, &tb, e))?;

        // Equality is whole-value for every shape, vectors included
        Ok(if op == BinOp::Equ { CTyp::Bool } else { t })
    }

    fn infer_pair(self, t: CRef<'_>, e: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        CTyp::lub_pair(&env.typ(t), &env.typ(e), kctx)
            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
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
        let Env { kctx, vctx, .. } = *env;
        // What kind of [t]?
        let k = kctx.get(&t.node).ok_or(TypeError::lub(
            TypeError::exp(kctx, vctx, self),
            LubError::kind_not_found(&t.node),
        ))?;
        if !k.is_scalar() {
            return Err(TypeError::challenge(kctx, vctx, &t.node, k));
        }
        // `x^0 == 1` for every `x`: nothing would be left to sample.
        if let Some(x) = x
            && let Exclusion::RootsOfUnity(n) = &x.node
            && n.node == 0
        {
            return Err(TypeError::located(
                &x.span,
                TypeError::excludes_all(kctx, vctx, &t.node),
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
        let Env { kctx, vctx, .. } = *env;
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
                    TypeError::exclusion_type(kctx, vctx, &t.node, &tv),
                ));
            }
        }
        Ok(typ)
    }

    fn infer_verify(self, exp: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, vctx, .. } = *env;
        let t = env.typ(exp);
        // The operand must be Bool (not Vec<Bool>)
        if t != CTyp::Bool {
            return Err(TypeError::located(
                exp.span(),
                TypeError::condition(kctx, vctx, self, &t),
            ));
        }
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
