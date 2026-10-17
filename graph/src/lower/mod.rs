//! Lowering a concrete module into Graph IR: one [`Dag`] per declaration.

use super::*;
use ark_ff::PrimeField;
use backend::{ABase, ATyp, Value, VirtualPolynomial};
use lang::ast::range::CRange;
use lang::ast::{
    BinOp, CBody, CExp, CExpr, CRef, CSig, Exp, ExpExclusion, ExpId, ExpLiteral, Expr, Exprs, Exps,
    Stmt,
};
use lang::id::{Fresh, Tid};
use lang::stack_guard;
use lang::typ::infer::TypeTable;
use lang::typ::{CKind, CTyp, CTyps, Distribution};
use num::{BigUint, ToPrimitive};
use share::traversal::ToTraversal1;

mod call;
mod map;
mod poly;
mod record;
mod vector;

/// The arena a tree is lowered in, with the types inferred for its nodes so far: lowering
/// infers every node it lowers, and new nodes are built over old ones, so each subtree is
/// inferred once rather than once per enclosing node.
pub(super) struct Arena {
    exprs: Exprs<BigUint>,
    types: TypeTable,
}

impl Arena {
    fn new(exprs: Exprs<BigUint>) -> Self {
        Self {
            exprs,
            types: TypeTable::new(),
        }
    }

    /// The type of node `id` under the given contexts.
    fn infer(
        &self,
        id: ExpId,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
    ) -> Result<CTyp, TypeError> {
        self.exprs
            .at(id)
            .infer_cached(kctx, &fctx.keys(), vctx, &self.types)
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
fn ark_error(
    kctx: &Ctx<Tid, CKind>,
    vctx: &Ctx<Vid, CTyp>,
    exp: CRef<'_>,
    typ: &CTyp,
) -> TypeError {
    TypeError::located(
        exp.span(),
        TypeError::next(
            TypeError::exp(kctx, vctx, exp),
            TypeError::ark(kctx, vctx, exp, typ),
        ),
    )
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

/// A collection of DAGs without annotations
impl<C: HasOpFactory> UDags<C> {
    /// Create a collection of Dags from a module
    ///
    /// One DAG is built per declaration, in module order. The full signature to
    /// body map is passed to every lowering so that calls can be inlined.
    ///
    /// # Errors
    /// Returns a [`GraphError`] if any declaration fails to lower — an unbound
    /// variable, a `lang`-level type error surfaced during inference, or a
    /// `fun` body outside the polynomial fragment.
    pub fn from_module(m: CModule) -> Result<Self, GraphError> {
        Self::build(m, true)
    }

    /// [`Self::from_module`] without lowering any protocol's `where` clause:
    /// each protocol keeps its `Node::Rel` marker but not the relation
    /// under it. Enough to project and run the prover and verifier, which
    /// never read the relation; the static analyses need the full graphs.
    ///
    /// A relation can be far larger than its protocol's body (one that
    /// ranges over every witness element lowers to a node per element), so
    /// this is what to build when only execution is wanted.
    ///
    /// # Errors
    /// As [`Self::from_module`], except that errors only lowering a relation
    /// would raise go unreported.
    pub fn from_module_for_execution(m: CModule) -> Result<Self, GraphError> {
        Self::build(m, false)
    }

    fn build(m: CModule, lower_relations: bool) -> Result<Self, GraphError> {
        let mut gs = UDags::new();

        let fctx = m
            .iter()
            .map(|(sig, body)| (sig.clone(), body.clone()))
            .collect::<Ctx<CSig, CBody>>();

        debug!("fctx: {}", fctx);
        for (sig, body) in m.into_iter() {
            debug!("Adding declaration: {}", sig);
            let mut g = UDag::new();
            g.add_decl(sig.clone(), body.clone(), &fctx, lower_relations)
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
    #[allow(clippy::too_many_arguments)]
    fn add_exclusion(
        &mut self,
        exprs: &mut Arena,
        exclusion: Option<Spanned<ExpExclusion<BigUint>>>,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
    ) -> Result<Option<OpExclusion<C>>, GraphError> {
        exclusion
            .map(|x| {
                x.node.try_map_values(|v| {
                    let span = exprs.span(v).clone();
                    let v =
                        self.add_exp(exprs, v, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
                    let typ = v.typ();
                    Ok(mk::<C>(self.materialize(v, edge_type, typ, span)))
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
    #[allow(clippy::too_many_arguments)]
    fn add_top_exp(
        &mut self,
        exp: CExpr,
        start: &mut NodeIndex,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        expected: Option<ATyp>,
    ) -> Result<(), GraphError> {
        debug!("Adding top-level expression: {exp}");
        let span = exp.span().clone();
        let Expr { exprs, root } = exp;
        let op = self.add_exp(
            &mut Arena::new(exprs),
            root,
            start,
            DepType::Data,
            kctx,
            fctx,
            vctx,
            vars,
            expected,
        )?;
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
        fctx: &Ctx<CSig, CBody>,
        lower_relation: bool,
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
                        TypeError::ark(
                            &kctx,
                            &vctx,
                            Expr::leaf(Exp::Var(arg.id.clone()), 0..0).root(),
                            &arg.typ,
                        ),
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

        // Typecheck the body with the type signature
        body.typecheck(sig.clone(), &fctx.keys())?;

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
                    self.add_top_exp(body, &mut start, &kctx, fctx, &vctx, &vars, None)?;
                }
                // Relation start: its own per-arg `Node::Arg` children so
                // walking the relation does not pull in the protocol body
                // through shared `Arg` nodes.
                let where_span = relation.span().clone();
                start = self.add_node(Node::rel(sig.name.node.clone()), where_span.clone());
                if lower_relation {
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
                    let rel_op = self.add_exp(
                        &mut Arena::new(relation_exprs),
                        relation,
                        &mut start,
                        DepType::Data,
                        &kctx,
                        fctx,
                        &vctx,
                        &vars,
                        None,
                    )?;
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
                    self.add_top_exp(body, &mut start, &kctx, fctx, &vctx, &vars, ret)?;
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
    #[allow(clippy::too_many_arguments)]
    #[stack_guard]
    fn add_exp(
        &mut self,
        exprs: &mut Arena,
        initial: ExpId,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        expected: Option<ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        let span = exprs.span(initial).clone();
        let mut expected = expected;
        let op = self.add_exp_raw(
            exprs,
            initial,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            &mut expected,
        )?;
        Ok(match expected {
            Some(target) if op.typ() != target => {
                let op = coerce_field_op(op, &target, 0);
                let atyp = op.typ();
                self.materialize(op, edge_type, atyp, span)
            }
            _ => op,
        })
    }

    /// [`Self::add_exp`] before the final coercion to `expected`, which only steers
    /// literals, the elements of vectors, records and map outputs, and inlined calls.
    #[allow(clippy::too_many_arguments)]
    fn add_exp_raw(
        &mut self,
        exprs: &mut Arena,
        initial: ExpId,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        expected: &mut Option<ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        // Own mutable copies for trampoline loop
        let mut id = initial;
        let mut vctx = vctx.clone();
        let mut vars = vars.clone();
        loop {
            // Type inference for [self]
            let typ = exprs.infer(id, kctx, fctx, &vctx)?;
            // Nodes created for this expression come from its source.
            let span = exprs.span(id).clone();
            // The contexts this iteration lowers `exp` under, for the arm helpers.
            macro_rules! step {
                () => {
                    Step {
                        exprs: &mut *exprs,
                        id,
                        typ: &typ,
                        span: span.clone(),
                        transcr: &mut *transcr,
                        edge_type,
                        kctx,
                        fctx,
                        vctx: &vctx,
                        vars: &vars,
                        expected: &mut *expected,
                    }
                };
            }
            // Convert [CExp] to [Op] while creating the graph
            match exprs[id].clone() {
                // A literal is an index unless it is field-only or a field element is expected
                CExp::Lit(n) => {
                    let field = expected.as_ref().is_some_and(ATyp::is_scalar);
                    return Ok(GOp::Value(literal_value::<C>(&n, &typ, field)));
                }

                // Unit value — no-op
                CExp::Unit => return Ok(GOp::Value(Value::Unit)),

                // Variables are edges, no new nodes are added
                CExp::Var(id) => return Self::op_from_var(&id, &vars),

                CExp::Evaluate(p, selector, opt_points) => {
                    return self.lower_evaluate(step!(), p, selector, opt_points);
                }

                CExp::Poly(v) => return self.lower_poly(step!(), v),

                CExp::Coef(v) => return self.lower_coef(step!(), v),

                // Lower CExp::Interpolate(opt_points, evals) into either Op::Ifft (unary)
                // or Op::Interpolate (binary) — monomorphic per variant.
                CExp::Interpolate(points_opt, evals) => {
                    return self.lower_interpolate(step!(), points_opt, evals);
                }
                // Create a new [vec] value; elements take the expected element type, else
                // the vector's own, so integers in a field vector become field elements.
                CExp::Vec(vs) => return self.lower_vec(step!(), vs),

                // MLE is a noop?
                // CExp::Mle(inner) => self.add_exp(exprs, inner, transcr, edge_type, kctx, fctx, &vctx, &vars),
                CExp::Mle(v) => return self.lower_mle(step!(), v),

                // Billinear pairing
                CExp::Pair(a, b) => return self.lower_pair(step!(), a, b),
                // Unary negation of a field element (including a negated integer literal):
                // `0 - x` in the field, with a finite `x` embedded first. Re-inferring a
                // rewritten `0 - 1` would subtract indices instead.
                CExp::Neg(a) if ATyp::from_ctyp(&typ, kctx).is_some_and(|t| t.is_scalar()) => {
                    return self.lower_neg(step!(), a);
                }
                // Any other unary negation: lower as 0 - x
                CExp::Neg(a) => {
                    let zero = exprs.push(Exp::Lit(<BigUint as ExpLiteral>::lit(0)), 0..0);
                    id = exprs.push(Exp::Bin(BinOp::Sub, zero, a), 0..0);
                    continue;
                }
                // Create a new [bin] node
                CExp::Bin(op, a, b) => return self.lower_bin(step!(), op, a, b),

                // Create a [range] value, no new nodes added
                CExp::Range(r) => return Ok(GOp::range(r)),

                CExp::Map(l, x, e) => return self.lower_map(step!(), l, x, e),

                CExp::Reduce(op, v) => return self.lower_reduce(step!(), op, v),
                CExp::Ram(a, b) => return self.lower_ram(step!(), a, b),
                CExp::Challenge(_, exclusion) => return self.lower_challenge(step!(), exclusion),
                CExp::Random(_, exclusion) => return self.lower_random(step!(), exclusion),
                CExp::App(fid, params) => match self.lower_app(step!(), fid, params)? {
                    Lowered::Rewrite(next) => id = next,
                    Lowered::Inline {
                        body,
                        vctx: callee_vctx,
                        vars: callee_vars,
                    } => {
                        id = body;
                        vctx = callee_vctx;
                        vars = callee_vars;
                    }
                },
                // Statements in order, each binding its variable for the rest of the block;
                // then the trampoline continues with the block's value.
                CExp::Block(stmts, tail) => {
                    for stmt in stmts {
                        self.lower_stmt(
                            exprs, stmt.node, transcr, edge_type, kctx, fctx, &mut vctx, &mut vars,
                        )?;
                    }
                    match tail {
                        Some(tail) => {
                            id = tail;
                            continue;
                        }
                        None => return Ok(GOp::Value(backend::Value::Unit)),
                    }
                }
                CExp::Verify(exp) => return self.lower_verify(step!(), exp),
                CExp::Fun(fun_vars, body) => return Self::lower_fun(exprs, fun_vars, body),
                CExp::Record(fields) => return self.lower_record(step!(), fields),
                CExp::Proj(record_exp, field_name) => {
                    return self.lower_proj(step!(), record_exp, field_name);
                }
                CExp::SetRecord(record_exp, field_name, value_exp) => {
                    return self.lower_set_record(step!(), record_exp, field_name, value_exp);
                }
            }
        } // end loop
    }
}

/// One expression in [`UDag::add_exp_raw`]'s loop: the expression, its inferred type and span,
/// and the contexts it is lowered under. The arm helpers take it so each keeps its own stack
/// frame out of the loop's (issue #252).
struct Step<'a, C: HasOpFactory> {
    exprs: &'a mut Arena,
    id: ExpId,
    typ: &'a CTyp,
    span: std::ops::Range<usize>,
    transcr: &'a mut NodeIndex,
    edge_type: DepType,
    kctx: &'a Ctx<Tid, CKind>,
    fctx: &'a Ctx<CSig, CBody>,
    vctx: &'a Ctx<Vid, CTyp>,
    vars: &'a Ctx<Vid, GOp<C>>,
    expected: &'a mut Option<ATyp>,
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
    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    fn lower_stmt(
        &mut self,
        exprs: &mut Arena,
        stmt: Stmt,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &mut Ctx<Vid, CTyp>,
        vars: &mut Ctx<Vid, GOp<C>>,
    ) -> Result<(), GraphError> {
        match stmt {
            Stmt::Let(id, l) => {
                // Infer the type of [l]
                let tl = exprs.infer(l, kctx, fctx, vctx)?;
                // Add left-hand side as node
                let nl =
                    self.add_exp(exprs, l, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
                if let GOp::Ref(r, _) = &nl {
                    self.bind(r.node(), &id);
                    self.transcript_vars.insert(&r.node(), &false);
                }
                // Add [id] to the variable context (clone-on-write)
                vctx.insert(&id.node, &tl);
                vars.insert(&id.node, &nl);
            }
            Stmt::Exp(l) => {
                self.add_exp(exprs, l, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
            }
            Stmt::Log(id, l) => {
                // A transcript node comes from the value sent.
                let sent = exprs.span(l).clone();
                // Infer the type of [l]
                let tl = exprs.infer(l, kctx, fctx, vctx)?;
                // Add left-hand side as node
                let ol =
                    self.add_exp(exprs, l, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
                // Record transcript interaction
                let transcr_op = self.log_transcript(transcr, &id, &ol, sent);
                // Add [id] to the variable context (clone-on-write)
                vctx.insert(&id.node, &tl);
                vars.insert(&id.node, &transcr_op);
            }
        }
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
    fn lower_pair(&mut self, step: Step<'_, C>, a: ExpId, b: ExpId) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let va = self.add_exp(exprs, a, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        let vb = self.add_exp(exprs, b, transcr, edge_type, kctx, fctx, vctx, vars, None)?;

        let atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;

        Ok(self.materialize(
            GOp::pair(va, vb, atyp.clone()),
            edge_type,
            atyp,
            span.clone(),
        ))
    }

    #[inline(never)]
    fn lower_neg(&mut self, step: Step<'_, C>, a: ExpId) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let child = self.add_exp(
            exprs,
            a,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            Some(ATyp::scalar()),
        )?;
        let zero = GOp::Value(Value::Scalar(C::F::from(0u64)));
        let bop = GOp::bin(BinOp::Sub, zero, child, ATyp::scalar());
        Ok(self.add_bin(bop, edge_type, ATyp::scalar(), span.clone()))
    }

    #[inline(never)]
    fn lower_bin(
        &mut self,
        step: Step<'_, C>,
        op: BinOp,
        a: ExpId,
        b: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        // Add children first
        let vl = self.add_exp(exprs, a, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        let vr = self.add_exp(exprs, b, transcr, edge_type, kctx, fctx, vctx, vars, None)?;

        // Convert type [typ] to [ATyp]
        let atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;

        let bop = field_bin(op, vl, vr, atyp.clone());
        Ok(self.add_bin(bop, edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    fn lower_challenge(
        &mut self,
        step: Step<'_, C>,
        exclusion: Option<Spanned<ExpExclusion<BigUint>>>,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let at =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        let exclusion =
            self.add_exclusion(exprs, exclusion, transcr, edge_type, kctx, fctx, vctx, vars)?;
        let nchallenge = self.add_node(Node::challenge(&at, exclusion.clone()), span.clone());
        self.add_edges(edge_type, nchallenge, GOp::Challenge(at.clone(), exclusion));
        // Add transcript edge to [nchallenge]
        self.add_edge(*transcr, nchallenge, Dep::transcript());
        // Update transcript node
        *transcr = nchallenge;

        Ok(GOp::underscore(nchallenge, at))
    }

    #[inline(never)]
    fn lower_random(
        &mut self,
        step: Step<'_, C>,
        exclusion: Option<Spanned<ExpExclusion<BigUint>>>,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let at =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        let exclusion =
            self.add_exclusion(exprs, exclusion, transcr, edge_type, kctx, fctx, vctx, vars)?;
        let nrand = self.add_node(Node::random(&at, exclusion.clone()), span.clone());
        self.add_edges(edge_type, nrand, GOp::Random(at.clone(), exclusion));
        Ok(GOp::underscore(nrand, at))
    }

    #[inline(never)]
    fn lower_verify(&mut self, step: Step<'_, C>, exp: ExpId) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let oa = self.add_exp(exprs, exp, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        // Add new node
        let nverify = self.add_node(Node::verify(&oa), span.clone());
        self.add_edges(edge_type, nverify, oa);
        // No transcript edge — the Op::Verify variant itself
        // marks the node as a verifier check.
        // Returns Unit value; sequencing via Let(None, ...) discards it.
        Ok(GOp::Value(backend::Value::Unit))
    }
}
