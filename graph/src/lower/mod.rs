//! Lowering a concrete module into Graph IR: one [`Dag`] per declaration.

use super::*;
use ark_ff::PrimeField;
use backend::{ABase, ATyp, Value, VirtualPolynomial};
use lang::ast::range::CRange;
use lang::ast::{
    BinOp, BodyTypes, CBody, CExp, CRef, CSig, Exp, ExpExclusion, ExpId, ExpLiteral, Expr, Exprs,
    Exps, TypedModule,
};
use lang::id::{Fresh, Tid};
use lang::stack_guard;
use lang::typ::infer::{Cx, TypeTable};
use lang::typ::{CKind, CTyp, CTyps, Distribution};
use num::{BigUint, ToPrimitive};
use share::traversal::ToTraversal1;

mod call;
mod map;
mod poly;
mod record;
mod vector;

/// The arena a tree is lowered in, with the types of its nodes: those the type check found,
/// and those of the nodes lowering adds, inferred from their children's.
pub(super) struct Arena {
    exprs: Exprs<BigUint>,
    types: TypeTable,
    /// The signatures calls resolve among.
    sigs: Set<CSig>,
}

impl Arena {
    fn new(exprs: Exprs<BigUint>, types: TypeTable, sigs: Set<CSig>) -> Self {
        Self { exprs, types, sigs }
    }

    /// The type of node `id`, under the given contexts if it is not typed yet.
    fn infer(
        &mut self,
        id: ExpId,
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
    ) -> Result<CTyp, TypeError> {
        self.exprs.at(id).infer(
            &Cx {
                kctx,
                fctx: &self.sigs,
                vctx,
            },
            &mut self.types,
        )
    }
}

impl std::ops::Deref for Arena {
    type Target = Exprs<BigUint>;
    fn deref(&self) -> &Exprs<BigUint> {
        &self.exprs
    }
}

impl std::ops::DerefMut for Arena {
    fn deref_mut(&mut self) -> &mut Exprs<BigUint> {
        &mut self.exprs
    }
}

/// `exp`, of type `typ`, has no Arkworks type; located at `exp`.
fn ark_error(kctx: &Ctx<Tid, CKind>, exp: CRef<'_>, typ: &CTyp) -> TypeError {
    TypeError::located(exp.span(), TypeError::Ark(kctx.clone(), typ.clone()))
}

/// The literal `n` in the field `C::F`, reduced modulo its prime from the complete magnitude.
fn field_from_literal<C: ArkConfig>(n: &BigUint) -> C::F {
    match n.to_u64() {
        Some(v) => C::F::from(v),
        None => C::F::from_le_bytes_mod_order(&n.to_bytes_le()),
    }
}

/// The constant for literal `n` of inferred type `typ`: a field element when `typ` is a
/// field-only literal or `field` asks for one, otherwise the finite index `n`.
fn literal_value<C: ArkConfig>(n: &BigUint, typ: &CTyp, field: bool) -> Value<C> {
    match typ {
        CTyp::Fin(r) if !field => Value::Index(r.start()),
        _ => Value::Scalar(field_from_literal::<C>(n)),
    }
}

/// Whether `t` is a finite index or a flat vector of them, the shapes `Op::ToScalar` embeds.
fn is_fin_shaped(t: &ATyp) -> bool {
    match t {
        ATyp::Base(ABase::Fin(_)) => true,
        ATyp::Vec(deref!(e), _) => e.is_fin(),
        _ => false,
    }
}

/// `op` with every finite-index leaf that `target` declares a field element embedded into
/// the field, folding constants. The caller has checked that the source type fits `target`;
/// any other difference (a wider index range, a lower polynomial degree) is left as is.
/// Compound vectors are converted with an `Op::Map` whose loop parameter has level
/// `loop_depth`, the number of enclosing loop binders.
///
/// # Panics
/// Panics if a vector's length differs from the target's, which source typing rules out.
fn coerce_field_op<C: HasOpFactory>(op: GOp<C>, target: &ATyp, loop_depth: usize) -> GOp<C> {
    let source = op.typ();
    if &source == target {
        return op;
    }
    match (&source, target) {
        (ATyp::Base(ABase::Fin(_)), ATyp::Base(ABase::Scalar)) => GOp::to_scalar(op),
        (ATyp::Vec(deref!(src), n), ATyp::Vec(deref!(tgt), m)) => {
            assert_eq!(n, m, "coerce_field_op: vector length mismatch");
            if src.is_fin() && tgt.is_scalar() {
                return GOp::to_scalar(op);
            }
            match op {
                Op::Vec(elems) => GOp::vec(
                    elems
                        .iter()
                        .map(|e| coerce_field_op(e.get().clone(), tgt, loop_depth))
                        .collect(),
                ),
                op => {
                    let elem = GOp::loop_param(loop_depth, src.clone());
                    let body = coerce_field_op(elem.clone(), tgt, loop_depth + 1);
                    if body == elem { op } else { GOp::map(op, body) }
                }
            }
        }
        (ATyp::Record(src_fields), ATyp::Record(tgt_fields)) => {
            let mut fields: Ctx<String, HOp<C>> = Ctx::new();
            for (name, tgt) in tgt_fields.iter() {
                let field = match &op {
                    Op::Record(ops) => ops[name].get().clone(),
                    op => GOp::proj(op.clone(), name.clone(), src_fields[name].clone()),
                };
                fields.insert(name, &mk::<C>(coerce_field_op(field, tgt, loop_depth)));
            }
            Op::Record(fields)
        }
        _ => op,
    }
}

/// Embeds a constant finite operand of an arithmetic or concatenation operator into the
/// field when the operator's `result` is not finite, so that `GOp::bin` folds field values
/// (and appends field elements to a field vector). A dynamic
/// operand is left to the runtime's mixed index/field arithmetic.
fn field_operand<C: HasOpFactory>(op: GOp<C>, result: &ATyp) -> GOp<C> {
    if matches!(op, Op::Value(_) | Op::Vec(_))
        && is_fin_shaped(&op.typ())
        && !result.into_inner().is_fin()
    {
        GOp::to_scalar(op)
    } else {
        op
    }
}

/// `GOp::bin(op, a, b, result)` with constant finite operands embedded into the field
/// first; a finite exponent stays an index.
fn field_bin<C: HasOpFactory>(op: BinOp, a: GOp<C>, b: GOp<C>, result: ATyp) -> GOp<C> {
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Dot | BinOp::Concat => GOp::bin(
            op,
            field_operand(a, &result),
            field_operand(b, &result),
            result,
        ),
        BinOp::Pow => GOp::bin(op, field_operand(a, &result), b, result),
        _ => GOp::bin(op, a, b, result),
    }
}

/// Whether lowering includes each protocol's `where` clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Relations {
    /// Lower it under the protocol's `Node::Rel` marker: the static analyses read it.
    Lower,
    /// Keep only the marker. Enough to project and run the prover and verifier, which never
    /// read the relation; a relation can be far larger than its protocol's body (one that
    /// ranges over every witness element lowers to a node per element).
    Skip,
}

/// A collection of DAGs without annotations
impl<C: HasOpFactory> UDags<C> {
    /// One DAG per declaration of `m`, in module order. The full signature to body map is
    /// passed to every lowering so that calls can be inlined.
    ///
    /// # Errors
    /// Returns a [`GraphError`] if a declaration fails to lower: a type without an Arkworks
    /// representation, or a `fun` body outside the polynomial fragment. With
    /// [`Relations::Skip`], errors only lowering a relation would raise go unreported.
    pub fn lower(m: &TypedModule, relations: Relations) -> Result<Self, GraphError> {
        let fctx = m
            .module()
            .iter()
            .map(|(sig, body)| (sig.clone(), body.clone()))
            .collect::<Ctx<CSig, CBody>>();
        let mut gs = UDags::new();
        for (sig, body, types) in m.iter() {
            debug!("Adding declaration: {}", sig);
            let mut g = UDag::new();
            g.add_decl(sig.clone(), body.clone(), types.clone(), &fctx, relations)
                .map_err(|e| e.located(&sig.name.span))?;
            gs.0.push(g);
        }
        Ok(gs)
    }
}

/// Constructors for graphs
impl<C: HasOpFactory> UDag<C> {
    /// Materialize an operation into the DAG.
    ///
    /// If `op` is already `Op::Ref` or `Op::Value`, it is returned as-is.
    /// Otherwise, a new DAG node is created for `op`, edges are added from
    /// that node to all `Op::Ref` children of `op`, and an `Op::Ref` to
    /// the new node is returned.
    ///
    /// This is the primary mechanism for enforcing `add_exp`'s invariant
    /// that its return value is always `Op::Ref` or `Op::Value`.
    fn materialize(
        &mut self,
        op: GOp<C>,
        edge_type: DepType,
        atyp: ATyp,
        span: std::ops::Range<usize>,
    ) -> GOp<C> {
        match &op {
            Op::Ref(_, _) | Op::Value(_) => op,
            _ => {
                let node = self.add_node(Node::Op(mk::<C>(op.clone()), Nothing), span);
                self.add_edges(edge_type, node, op);
                GOp::underscore(node, atyp)
            }
        }
    }

    /// Adds the vector a sample excludes, if it lists one, as a node or a
    /// literal, and returns the exclusion for the sample's operation.
    fn add_exclusion(
        &mut self,
        scope: &mut Scope<'_, C>,
        exclusion: Option<Spanned<ExpExclusion<BigUint>>>,
    ) -> Result<Option<OpExclusion<C>>, GraphError> {
        exclusion
            .map(|x| {
                x.node.try_map_values(|v| {
                    let span = scope.exprs.span(v).clone();
                    let v = self.add_exp(scope, v, None)?;
                    let typ = v.typ();
                    Ok(mk::<C>(self.materialize(v, scope.edge_type, typ, span)))
                })
            })
            .transpose()
    }

    /// Adds `bop`, a `GOp::bin` result of type `atyp`: a `Node::bin` when it stayed a
    /// binary operation, otherwise the materialized folded operation.
    fn add_bin(
        &mut self,
        bop: GOp<C>,
        edge_type: DepType,
        atyp: ATyp,
        span: std::ops::Range<usize>,
    ) -> GOp<C> {
        if let GOp::Bin(op, vl, vr, atyp) = bop {
            let nbin = self.add_node(Node::bin(op, &vl, &vr, &atyp), span);
            self.add_edges(edge_type, nbin, (*vl).clone());
            self.add_edges(edge_type, nbin, (*vr).clone());
            GOp::underscore(nbin, atyp)
        } else {
            self.materialize(bop, edge_type, atyp, span)
        }
    }

    /// Add a new top-level expression to the graph; `expected` is the declared type its
    /// value must take (a function's return type), if any.
    fn add_top_exp(
        &mut self,
        scope: &mut Scope<'_, C>,
        root: ExpId,
        expected: Option<ATyp>,
    ) -> Result<(), GraphError> {
        let span = scope.exprs.span(root).clone();
        debug!("Adding top-level expression at {:?}", span);
        let op = self.add_exp(scope, root, expected)?;
        if !op.is_ref() {
            let nr = self.add_node(Node::ret(&op), span);
            self.add_edges(DepType::Data, nr, op);
        };
        Ok(())
    }

    /// Add a new declaration to the graph. With `lower_relation` unset, a
    /// protocol's `where` clause is left out: only its `Node::Rel` marker is
    /// added.
    fn add_decl(
        &mut self,
        sig: CSig,
        body: CBody,
        types: BodyTypes,
        fctx: &Ctx<CSig, CBody>,
        relations: Relations,
    ) -> Result<(), GraphError> {
        // Kind context
        let kctx = sig.typevars.to_ctx();
        // Add arguments to [vctx] and [vars]
        let mut vctx = Ctx::new();

        // Source bindings of the arguments, recorded on their nodes for diagnostics.
        let arg_ids: HashMap<&Vid, &Spanned<Vid>> =
            sig.args.iter().map(|arg| (&arg.id.node, &arg.id)).collect();
        // Build a lookup from arg name → (qualifier, distribution) for Node::Arg construction.
        let arg_meta: HashMap<&Vid, (Qualifier, Distribution)> = sig
            .args
            .iter()
            .map(|arg| (&arg.id.node, (arg.qualifier.node, arg.distribution.node)))
            .collect();

        // Add arguments to type and fft contexts
        let mut atyps = Ctx::new();
        for arg in sig.args.iter() {
            let at = ATyp::from_ctyp(&arg.typ, &kctx).ok_or_else(|| {
                TypeError::decl(
                    &sig.name,
                    TypeError::located(
                        &arg.id.span,
                        TypeError::Ark(kctx.clone(), arg.typ.node.clone()),
                    ),
                )
            })?;
            atyps.insert(&arg.id.node, &at);
            vctx.insert(&arg.id.node, &arg.typ.node);
        }
        // Expose singleton range typevars (e.g. N: 4) as term-level constants.
        for (tid, kind) in kctx.iter() {
            if let CKind::Range(r) = kind
                && r.step() == 1
                && r.end() == r.start() + 1
            {
                vctx.insert(&Vid::new(&tid.0), &CTyp::Fin(r.clone()));
            }
        }

        // Add the body to the Graph
        match body {
            CBody::Proto { body, relation } => {
                debug!("Adding proto: {:?}", sig);
                // Start node (input marker)
                let mut start =
                    self.add_node(Node::inp(sig.name.node.clone()), sig.name.span.clone());
                let mut vars: Ctx<Vid, GOp<C>> = Ctx::new();
                for (id, typ) in atyps.iter() {
                    let (qualifier, distribution) = arg_meta
                        .get(id)
                        .copied()
                        .expect("arg meta must be present for every sig arg");
                    let arg_node = self.add_node(
                        Node::arg(
                            id.clone(),
                            typ.clone(),
                            qualifier,
                            distribution,
                            ArgKind::Input,
                        ),
                        arg_ids[id].span.clone(),
                    );
                    self.graph.add_edge(start, arg_node, Dep::data());
                    self.bind(arg_node, arg_ids[id]);
                    vars.insert(id, &GOp::var(id, arg_node, typ.clone()));
                }
                for (tid, kind) in kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step() == 1
                        && r.end() == r.start() + 1
                    {
                        let vid = Vid::new(&tid.0);
                        vars.insert(&vid, &GOp::Value(Value::Index(r.start())));
                    }
                }
                if let Some(body) = body {
                    let Expr { exprs, root } = body;
                    let mut arena = Arena::new(exprs, types.body, fctx.keys());
                    let mut scope = Scope {
                        exprs: &mut arena,
                        transcr: &mut start,
                        edge_type: DepType::Data,
                        kctx: &kctx,
                        fctx,
                        vctx: vctx.clone(),
                        vars,
                    };
                    self.add_top_exp(&mut scope, root, None)?;
                }
                // Relation start: its own per-arg `Node::Arg` children so
                // walking the relation does not pull in the protocol body
                // through shared `Arg` nodes.
                let where_span = relation.span().clone();
                start = self.add_node(Node::rel(sig.name.node.clone()), where_span.clone());
                if relations == Relations::Lower {
                    let mut vars: Ctx<Vid, GOp<C>> = Ctx::new();
                    for (id, typ) in atyps.iter() {
                        let (qualifier, distribution) = arg_meta
                            .get(id)
                            .copied()
                            .expect("arg meta must be present for every sig arg");
                        let arg_node = self.add_node(
                            Node::arg(
                                id.clone(),
                                typ.clone(),
                                qualifier,
                                distribution,
                                ArgKind::Relation,
                            ),
                            arg_ids[id].span.clone(),
                        );
                        self.graph.add_edge(start, arg_node, Dep::data());
                        self.bind(arg_node, arg_ids[id]);
                        vars.insert(id, &GOp::var(id, arg_node, typ.clone()));
                    }
                    for (tid, kind) in kctx.iter() {
                        if let CKind::Range(r) = kind
                            && r.step() == 1
                            && r.end() == r.start() + 1
                        {
                            let vid = Vid::new(&tid.0);
                            vars.insert(&vid, &GOp::Value(Value::Index(r.start())));
                        }
                    }
                    // Lower the relation as a single Bool expression and wrap it
                    // in an Assert node. The `where` clause infers to Bool, and
                    // this is the only Assert in the graph: `assert` is not part
                    // of the language, so the analyses never meet a condition the
                    // developer states.
                    let Expr {
                        exprs: relation_exprs,
                        root: relation,
                    } = relation;
                    let mut arena = Arena::new(relation_exprs, types.relation, fctx.keys());
                    let mut scope = Scope {
                        exprs: &mut arena,
                        transcr: &mut start,
                        edge_type: DepType::Data,
                        kctx: &kctx,
                        fctx,
                        vctx: vctx.clone(),
                        vars,
                    };
                    let rel_op = self.add_exp(&mut scope, relation, None)?;
                    let nassert = self.add_node(Node::assert(&rel_op), where_span);
                    self.add_edges(DepType::Data, nassert, rel_op);
                }
            }
            CBody::Func { body } => {
                let mut start =
                    self.add_node(Node::inp(sig.name.node.clone()), sig.name.span.clone());
                let mut vars: Ctx<Vid, GOp<C>> = Ctx::new();
                for (id, typ) in atyps.iter() {
                    let (qualifier, distribution) = arg_meta
                        .get(id)
                        .copied()
                        .expect("arg meta must be present for every sig arg");
                    let arg_node = self.add_node(
                        Node::arg(
                            id.clone(),
                            typ.clone(),
                            qualifier,
                            distribution,
                            ArgKind::Input,
                        ),
                        arg_ids[id].span.clone(),
                    );
                    self.graph.add_edge(start, arg_node, Dep::data());
                    self.bind(arg_node, arg_ids[id]);
                    vars.insert(id, &GOp::var(id, arg_node, typ.clone()));
                }
                for (tid, kind) in kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step() == 1
                        && r.end() == r.start() + 1
                    {
                        let vid = Vid::new(&tid.0);
                        vars.insert(&vid, &GOp::Value(Value::Index(r.start())));
                    }
                }
                if let Some(body) = body {
                    // The body's value takes the declared return type.
                    let ret = sig
                        .ret
                        .as_ref()
                        .and_then(|ret| ATyp::from_ctyp(&ret.node, &kctx));
                    let Expr { exprs, root } = body;
                    let mut arena = Arena::new(exprs, types.body, fctx.keys());
                    let mut scope = Scope {
                        exprs: &mut arena,
                        transcr: &mut start,
                        edge_type: DepType::Data,
                        kctx: &kctx,
                        fctx,
                        vctx: vctx.clone(),
                        vars,
                    };
                    self.add_top_exp(&mut scope, root, ret)?;
                }
            }
            CBody::TypeAlias => {
                // Type aliases are expanded inline during module parsing,
                // no graph nodes needed.
            }
        }

        Ok(())
    }

    /// Variables to operations by lookup in [vars]
    fn op_from_var(id: &Spanned<Vid>, vars: &Ctx<Vid, GOp<C>>) -> Result<GOp<C>, GraphError> {
        vars.get(&id.node)
            .cloned()
            .ok_or_else(|| GraphError::var_not_found(id))
    }

    /// Add an expression [exp] to the graph.
    /// Convert a `CExp` to a `GOp` while creating the graph.
    ///
    /// # Invariant
    ///
    /// This method guarantees that its return value is always `Op::Ref` or
    /// `Op::Value`. Compound operations that would produce other variants
    /// (e.g., `Op::Bin`, `Op::Vec`, `Op::Record`) are *materialized*: a DAG
    /// node is created, edges are added, and an `Op::Ref` to the new node is
    /// returned. The sole exception is the trampoline loop body, which may
    /// produce intermediate non-Ref values that are consumed by later
    /// iterations (e.g., `CExp::Block` bindings, `CExp::App` inlining).
    ///
    /// Downstream consumers (notably `trans_clos_op` and `ref_vars` in the
    /// Groebner analysis) rely on this invariant: every top-level result from
    /// `add_exp` can be assumed to be a `Ref` or `Value`.
    ///
    /// `expected` is the declared type the value must take, if known (a function's return
    /// type, a formal argument, a record field): finite-index leaves it declares field
    /// elements are embedded into the field, before materializing (see
    /// [`coerce_field_op`]). Inlining a call adopts the callee's return type when the
    /// caller has no expectation.
    #[stack_guard]
    fn add_exp(
        &mut self,
        scope: &mut Scope<'_, C>,
        initial: ExpId,
        mut expected: Option<ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        let span = scope.exprs.span(initial).clone();
        let op = self.add_exp_raw(&mut scope.nested(), initial, &mut expected)?;
        Ok(match expected {
            Some(target) if op.typ() != target => {
                let op = coerce_field_op(op, &target, 0);
                let atyp = op.typ();
                self.materialize(op, scope.edge_type, atyp, span)
            }
            _ => op,
        })
    }

    /// [`Self::add_exp`] before the final coercion to `expected`, which only steers
    /// literals, the elements of vectors, records and map outputs, and inlined calls.
    fn add_exp_raw(
        &mut self,
        scope: &mut Scope<'_, C>,
        initial: ExpId,
        expected: &mut Option<ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        let mut id = initial;
        loop {
            // Type inference for [self]
            let typ = scope.infer(id)?;
            // Nodes created for this expression come from its source.
            let span = scope.exprs.span(id).clone();
            // Convert [CExp] to [Op] while creating the graph
            match scope.exprs[id].clone() {
                // A literal is an index unless it is field-only or a field element is expected
                CExp::Lit(n) => {
                    let field = expected.as_ref().is_some_and(ATyp::is_scalar);
                    return Ok(GOp::Value(literal_value::<C>(&n, &typ, field)));
                }

                // Unit value — no-op
                CExp::Unit => return Ok(GOp::Value(Value::Unit)),

                // Variables are edges, no new nodes are added
                CExp::Var(id) => return Self::op_from_var(&id, &scope.vars),

                CExp::Evaluate(p, selector, opt_points) => {
                    return self.lower_evaluate(scope, id, p, selector, opt_points);
                }

                CExp::Poly(v) => return self.lower_poly(scope, id, v),

                CExp::Coef(v) => return self.lower_coef(scope, id, v),

                // Lower CExp::Interpolate(opt_points, evals) into either Op::Ifft (unary)
                // or Op::Interpolate (binary) — monomorphic per variant.
                CExp::Interpolate(points_opt, evals) => {
                    return self.lower_interpolate(scope, id, points_opt, evals);
                }
                // Create a new [vec] value; elements take the expected element type, else
                // the vector's own, so integers in a field vector become field elements.
                CExp::Vec(vs) => return self.lower_vec(scope, id, vs, expected.as_ref()),

                // MLE is a noop?
                // CExp::Mle(inner) => self.add_exp(scope, inner, None),
                CExp::Mle(v) => return self.lower_mle(scope, id, v),

                // Billinear pairing
                CExp::Pair(a, b) => return self.lower_pair(scope, id, a, b),
                // Unary negation of a field element (including a negated integer literal):
                // `0 - x` in the field, with a finite `x` embedded first. Re-inferring a
                // rewritten `0 - 1` would subtract indices instead.
                CExp::Neg(a)
                    if ATyp::from_ctyp(&typ, scope.kctx).is_some_and(|t| t.is_scalar()) =>
                {
                    return self.lower_neg(scope, id, a);
                }
                // Any other unary negation: lower as 0 - x
                CExp::Neg(a) => {
                    let zero = scope
                        .exprs
                        .push(Exp::Lit(<BigUint as ExpLiteral>::lit(0)), span.clone());
                    id = scope.exprs.push(Exp::Bin(BinOp::Sub, zero, a), span);
                    continue;
                }
                // Create a new [bin] node
                CExp::Bin(op, a, b) => return self.lower_bin(scope, id, op, a, b),

                // Create a [range] value, no new nodes added
                CExp::Range(r) => return Ok(GOp::range(r)),

                CExp::Map(l, x, e) => return self.lower_map(scope, id, l, x, e, expected.as_ref()),

                CExp::Reduce(op, v) => return self.lower_reduce(scope, id, op, v),
                CExp::Ram(a, b) => return self.lower_ram(scope, id, a, b),
                CExp::Challenge(_, exclusion) => return self.lower_challenge(scope, id, exclusion),
                CExp::Random(_, exclusion) => return self.lower_random(scope, id, exclusion),
                CExp::App(fid, params) => match self.lower_app(scope, id, fid, params, expected)? {
                    Lowered::Rewrite(next) => id = next,
                    Lowered::Inline {
                        body,
                        vctx: callee_vctx,
                        vars: callee_vars,
                    } => {
                        id = body;
                        scope.vctx = callee_vctx;
                        scope.vars = callee_vars;
                    }
                },
                // Statements in order, each binding its variable for the rest of the block;
                // then the trampoline continues with the block's value.
                CExp::Block(stmts, tail) => {
                    for stmt in stmts {
                        self.lower_stmt(scope, stmt)?;
                    }
                    match tail {
                        Some(tail) => {
                            id = tail;
                            continue;
                        }
                        None => return Ok(GOp::Value(backend::Value::Unit)),
                    }
                }
                CExp::Let(..) | CExp::Log(..) | CExp::Discard(_) => {
                    unreachable!("statements are lowered with their block")
                }
                CExp::Verify(exp) => return self.lower_verify(scope, id, exp),
                CExp::Fun(fun_vars, body) => return Self::lower_fun(scope.exprs, fun_vars, body),
                CExp::Record(fields) => {
                    return self.lower_record(scope, id, fields, expected.as_ref());
                }
                CExp::Proj(record_exp, field_name) => {
                    return self.lower_proj(scope, id, record_exp, field_name);
                }
                CExp::SetRecord(record_exp, field_name, value_exp) => {
                    return self.lower_set_record(scope, id, record_exp, field_name, value_exp);
                }
            }
        } // end loop
    }
}

/// The state shared while lowering a tree. Nested expressions clone the persistent variable
/// contexts, while sharing the arena and the current transcript node.
struct Scope<'a, C: HasOpFactory> {
    exprs: &'a mut Arena,
    transcr: &'a mut NodeIndex,
    edge_type: DepType,
    kctx: &'a Ctx<Tid, CKind>,
    fctx: &'a Ctx<CSig, CBody>,
    vctx: Ctx<Vid, CTyp>,
    vars: Ctx<Vid, GOp<C>>,
}

impl<C: HasOpFactory> Scope<'_, C> {
    fn infer(&mut self, id: ExpId) -> Result<CTyp, TypeError> {
        self.exprs.infer(id, self.kctx, &self.vctx)
    }

    fn nested(&mut self) -> Scope<'_, C> {
        Scope {
            exprs: self.exprs,
            transcr: self.transcr,
            edge_type: self.edge_type,
            kctx: self.kctx,
            fctx: self.fctx,
            vctx: self.vctx.clone(),
            vars: self.vars.clone(),
        }
    }
}

/// How lowering continues after an application that [`UDag::add_exp_raw`] does not lower
/// directly: every application is rewritten or inlined, then lowered in the same loop.
enum Lowered<C: HasOpFactory> {
    /// Lower this expression in the application's place (polynomial and MLE evaluation).
    Rewrite(ExpId),
    /// Lower an inlined function body under the callee's variable contexts.
    Inline {
        body: ExpId,
        vctx: Ctx<Vid, CTyp>,
        vars: Ctx<Vid, GOp<C>>,
    },
}

/// The arms of [`UDag::add_exp_raw`] kept in this module; the larger groups live in the `call`,
/// `poly`, `record` and `vector` submodules.
impl<C: HasOpFactory> UDag<C> {
    /// Lowers one statement of a block, binding its variable in `vctx` and `vars` for the rest
    /// of the block.
    #[inline(never)]
    fn lower_stmt(&mut self, scope: &mut Scope<'_, C>, stmt: ExpId) -> Result<(), GraphError> {
        let node = scope.exprs[stmt].clone();
        let (CExp::Let(_, value) | CExp::Log(_, value) | CExp::Discard(value)) = node else {
            unreachable!("a block's statements are statements")
        };
        let op = self.add_exp(scope, value, None)?;
        let Some(x) = node.binder() else {
            return Ok(());
        };
        let op = if matches!(node, CExp::Log(..)) {
            // A transcript node comes from the value sent.
            let sent = scope.exprs.span(value).clone();
            self.log_transcript(scope.transcr, x, &op, sent)
        } else {
            if let GOp::Ref(r, _) = &op {
                self.bind(r.node(), x);
                self.transcript_vars.insert(&r.node(), &false);
            }
            op
        };
        // A statement has its value's type.
        let typ = scope.infer(stmt)?;
        scope.vctx.insert(&x.node, &typ);
        scope.vars.insert(&x.node, &op);
        Ok(())
    }

    /// The transcript operation `id <- ol` records, sent from `sent`: the node itself when it is
    /// already a transcript node with no other name, else a new transcript node wrapping it.
    #[inline(never)]
    fn log_transcript(
        &mut self,
        transcr: &mut NodeIndex,
        id: &Spanned<Vid>,
        ol: &GOp<C>,
        sent: std::ops::Range<usize>,
    ) -> GOp<C> {
        match ol {
            GOp::Ref(r, _)
                if self[r.node()].is_transcript()
                    && self.binding(r.node()).is_none_or(|b| b.node == id.node) =>
            {
                let n = r.node();
                // Node is already a transcript node and either has no name
                // or the same name — register directly.
                self.bind(n, id);
                self.transcript_vars.insert(&n, &true);
                GOp::Ref(Ref(n), ol.typ())
            }
            GOp::Ref(r, _) => {
                let n = r.node();
                // Reuse: create a wrapper transcript node.
                let nl = self.add_node(Node::transcr(&GOp::Ref(Ref(n), ol.typ())), sent.clone());
                self.add_edges(DepType::Data, nl, ol.clone());
                self.add_edge(*transcr, nl, Dep::transcript());
                self.node_mut(nl).set_transcript();
                self.bind(nl, id);
                self.transcript_vars.insert(&nl, &true);
                *transcr = nl;
                GOp::Ref(Ref(nl), ol.typ())
            }
            _ => {
                // Add new transcript node
                let nl = self.add_node(Node::transcr(ol), sent.clone());
                self.add_edges(DepType::Data, nl, ol.clone());
                self.add_edge(*transcr, nl, Dep::transcript());
                self.node_mut(nl).set_transcript();
                self.bind(nl, id);
                self.transcript_vars.insert(&nl, &true);
                *transcr = nl;
                GOp::Ref(Ref(nl), ol.typ())
            }
        }
    }

    #[inline(never)]
    fn lower_pair(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        a: ExpId,
        b: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let va = self.add_exp(scope, a, None)?;
        let vb = self.add_exp(scope, b, None)?;

        let atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;

        Ok(self.materialize(
            GOp::pair(va, vb, atyp.clone()),
            scope.edge_type,
            atyp,
            span.clone(),
        ))
    }

    #[inline(never)]
    fn lower_neg(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        a: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let span = scope.exprs.span(id).clone();
        let child = self.add_exp(scope, a, Some(ATyp::scalar()))?;
        let zero = GOp::Value(Value::Scalar(C::F::from(0u64)));
        let bop = GOp::bin(BinOp::Sub, zero, child, ATyp::scalar());
        Ok(self.add_bin(bop, scope.edge_type, ATyp::scalar(), span.clone()))
    }

    #[inline(never)]
    fn lower_bin(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        op: BinOp,
        a: ExpId,
        b: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        // Add children first
        let vl = self.add_exp(scope, a, None)?;
        let vr = self.add_exp(scope, b, None)?;

        // Convert type [typ] to [ATyp]
        let atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;

        let bop = field_bin(op, vl, vr, atyp.clone());
        Ok(self.add_bin(bop, scope.edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    fn lower_challenge(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        exclusion: Option<Spanned<ExpExclusion<BigUint>>>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let at = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        let exclusion = self.add_exclusion(scope, exclusion)?;
        let nchallenge = self.add_node(Node::challenge(&at, exclusion.clone()), span.clone());
        self.add_edges(
            scope.edge_type,
            nchallenge,
            GOp::Challenge(at.clone(), exclusion),
        );
        // Add transcript edge to [nchallenge]
        self.add_edge(*scope.transcr, nchallenge, Dep::transcript());
        // Update transcript node
        *scope.transcr = nchallenge;

        Ok(GOp::underscore(nchallenge, at))
    }

    #[inline(never)]
    fn lower_random(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        exclusion: Option<Spanned<ExpExclusion<BigUint>>>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let at = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        let exclusion = self.add_exclusion(scope, exclusion)?;
        let nrand = self.add_node(Node::random(&at, exclusion.clone()), span.clone());
        self.add_edges(scope.edge_type, nrand, GOp::Random(at.clone(), exclusion));
        Ok(GOp::underscore(nrand, at))
    }

    #[inline(never)]
    fn lower_verify(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        exp: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let span = scope.exprs.span(id).clone();
        let oa = self.add_exp(scope, exp, None)?;
        // Add new node
        let nverify = self.add_node(Node::verify(&oa), span.clone());
        self.add_edges(scope.edge_type, nverify, oa);
        // No transcript edge — the Op::Verify variant itself
        // marks the node as a verifier check.
        // Returns Unit value; sequencing via Let(None, ...) discards it.
        Ok(GOp::Value(backend::Value::Unit))
    }
}
