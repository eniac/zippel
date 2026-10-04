use crate::TransClos;
use crate::Var;
use graph::eval::collect_refs;
use graph::{GOp, HOp, Op, Ref};
use lang::ast::BinOp;
use std::collections::{HashMap, HashSet};

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig};

mod combinatorics;

mod namespace;
pub use namespace::{GB_GENERATED_NAME_PREFIX, IdealNamespace};

#[allow(clippy::module_inception)]
mod ideal;
pub use ideal::{Check, Ideal, Origin, Stage};

/// A short name for `op`'s operation, for reporting where generators come from.
pub fn op_label<C: ArkConfig>(op: &GOp<C>) -> &'static str {
    match op {
        Op::Value(_) => "literal",
        Op::Ref(..) => "alias",
        Op::Bin(bop, ..) => match bop {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Pow => "^",
            BinOp::Dot => "dot",
            BinOp::Equ => "==",
            BinOp::And => "&&",
            BinOp::Concat => "++",
        },
        Op::Ram(..) => "index",
        Op::Vec(_) => "vec",
        Op::Record(_) => "record",
        Op::Random(..) => "random",
        Op::Pair(..) => "pair",
        Op::Challenge(..) => "challenge",
        Op::Ifft(_) => "ifft",
        Op::Interpolate(..) => "interpolate",
        Op::Fft(_) => "fft",
        Op::Poly(_) => "poly",
        Op::Mle(_) => "mle",
        Op::Proj(..) => "proj",
        Op::Coef(_) => "coef",
        Op::ToScalar(_) => "to_scalar",
        Op::Evaluate(..) => "eval",
        Op::LoopParam(..) => "loop-param",
        Op::Map(..) => "map",
        Op::ReduceMap(bop, ..) | Op::Reduce(bop, _) => match bop {
            BinOp::Add => "reduce(+)",
            BinOp::Sub => "reduce(-)",
            BinOp::Mul => "reduce(*)",
            BinOp::And => "reduce(&&)",
            _ => "reduce",
        },
        Op::Assert(_) => "assert",
        Op::Verify(_) => "verify",
    }
}

mod poly_source;
pub(crate) use poly_source::PolySource;

mod ops;
pub(crate) use ops::div::is_division_witness;
use ops::{EncodeCtx, link_to_polys};

/// Encoding choices only the completeness analysis makes. The default
/// reproduces the encoding the soundness and knowledge analyses rely on.
#[derive(Clone, Debug, Default)]
pub struct EncodeOptions {
    /// Split an asserted or verified `reduce(&&, v)` into one constraint per
    /// element of `v`, as the unrolled chain `v[0] && v[1] && …` would be,
    /// instead of asserting the product of the elements.
    pub split_reductions: bool,
    /// The `assert` nodes that wrap the `where` clause. When set, every other
    /// `assert` is a runtime check written in a protocol body and encodes to
    /// nothing: it is neither an assumption nor an obligation.
    pub relation_asserts: Option<HashSet<Ref>>,
    /// Encode `t = a / b`, for a divisor `b` that is not a known constant and a
    /// dividend `a` that is not a nonzero constant, as the definition
    /// `t := a·ι` next to `b·ι − 1`, instead of the constraint `a − b·t`. Both
    /// generate the same ideal, but the definition is substituted away, while
    /// `a − b·t` stays a generator whose leading term usually lies in `a`.
    pub division_definitions: bool,
    /// Put what each `verify` requires, `b − 1` per checked bool, in
    /// [`Ideal::goals`] instead of the generating set, so that one build of
    /// the verifier yields both its computation and what it checks.
    pub separate_goals: bool,
}

/// One bool an `assert` or `verify` requires to hold: a leaf of its `&&`
/// chain, or with [`EncodeOptions::split_reductions`], an element of a
/// `reduce(&&, …)` in it.
#[derive(Clone)]
pub(crate) struct AndLeaf<C: ArkConfig> {
    /// A `Bool` expression or, with `index`, a `Vec<Bool>` one.
    pub exp: HOp<C>,
    /// The element of `exp` this leaf is.
    pub index: Option<usize>,
    /// The outermost `reduce(&&, …)` node this leaf was split out of.
    pub reduction: Option<Ref>,
}

impl<C: ArkConfig> AndLeaf<C> {
    /// The graph nodes the leaf reads, including the reduction it was split
    /// out of.
    pub fn refs(&self) -> Vec<Ref> {
        let mut refs = collect_refs(self.exp.get());
        refs.extend(self.reduction);
        refs
    }
}

/// Constructs `Ideal`s from `TransClos` inputs. Owns a
/// `IdealNamespace` for division-witness and sentinel allocation
/// that persists across `build()` calls. Each call to `build(TransClos)`
/// returns a fresh `Ideal` with its own `vars` namespace.
#[derive(Clone)]
pub struct IdealBuilder<C: ArkConfig> {
    /// Name and sentinel allocator, shared by every `build()` call so that
    /// generated division witnesses and sentinels stay globally unique.
    pub ns: IdealNamespace<C>,
    /// Map from Ref to the GOp that produced it, for tracing `&&` chains
    /// in assert/verify operands back to their leaf bools.
    node_ops: HashMap<Ref, GOp<C>>,
    /// Encoding choices; see [`EncodeOptions`].
    options: EncodeOptions,
    /// With [`EncodeOptions::split_reductions`]: the variable bound to each
    /// element of a `Map` or `ReduceMap(&&)` result, keyed by the result.
    /// Those exist only inside the encoding, as sentinels.
    elements: HashMap<Ref, Vec<Var>>,
}

impl<C: ArkConfig + HasOpFactory> Default for IdealBuilder<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    /// Creates a builder with an empty namespace and no recorded node
    /// operations.
    pub fn new() -> Self {
        Self::with_options(EncodeOptions::default())
    }

    /// Creates a builder like [`Self::new`] that encodes as `options` says.
    pub fn with_options(options: EncodeOptions) -> Self {
        Self {
            ns: IdealNamespace::new(),
            node_ops: HashMap::new(),
            options,
            elements: HashMap::new(),
        }
    }

    /// The encoding choices this builder makes.
    pub fn options(&self) -> &EncodeOptions {
        &self.options
    }

    /// Build a `Ideal` from a `TransClos`. Each call returns a
    /// fresh ideal with its own `vars` namespace, while the builder
    /// namespace keeps generated witness/sentinel allocation stable.
    pub fn build(&mut self, tc: TransClos<C>) -> Ideal<C> {
        let mut ideal = Ideal::new();
        for new_arg in tc.vars.iter() {
            ideal.register(new_arg);
        }
        for (var, _op) in tc.clos.iter() {
            ideal.register(var);
        }

        // Build Ref → GOp map for tracing && chains in assert/verify.
        for (var, op) in tc.clos.iter() {
            self.node_ops.insert(var.reference, op.clone());
        }

        for (var, op) in tc.clos.into_iter() {
            // Every generator this node's encoding emits came from it.
            let before = ideal.generating_set.len();
            let aligned = ideal.origins_aligned();
            let label = op_label(&op);
            self.add_op(var.clone(), op, &mut ideal);
            if aligned {
                let origin = Origin {
                    stage: Stage::Unknown,
                    node: var.clone(),
                    op: label,
                };
                let emitted = ideal.generating_set.len() - before;
                ideal.origins.extend(std::iter::repeat_n(origin, emitted));
            }
            ideal.var_order.push(var);
        }
        ideal
    }

    pub(crate) fn sentinel_var(&mut self, name: &str, typ: ATyp, ideal: &mut Ideal<C>) -> Var {
        let var = self.ns.sentinel_var(name, typ);
        ideal.var_order.push(var.clone());
        var
    }

    /// Collect leaf bool expressions from an `&&` chain by tracing `Ref`
    /// nodes through the `node_ops` map. When the operand is a `Ref` to a
    /// `BinOp::And` node, recursively traces both sides. Non-`And` operands
    /// are collected as leaves.
    ///
    /// With [`EncodeOptions::split_reductions`], `reduce(&&, v)` over a
    /// `Vec<Bool>` contributes one leaf per element of `v`, as the unrolled
    /// chain `v[0] && v[1] && …` would; an element that is itself such a
    /// chain is split further. This relies on bools being 0 or 1, as
    /// splitting `&&` already does. The elements of a `Map` or `ReduceMap(&&)`
    /// result are the variables its encoding recorded, so that node must have
    /// been encoded first.
    ///
    /// Aliases are not traced. The graph only makes them for `t <- …` of a
    /// value already computed, and a check of `t` is a check of the message:
    /// what computed it belongs to the prover's encoding, a separate build.
    ///
    /// TODO(egg): This is a manual, ad-hoc peeling of `&&` chains to avoid
    /// high-degree product polynomials in the GB generating set. Once the
    /// planned `egg`-based optimization layer is in place (see upstream PR),
    /// this should be replaced by a proper e-graph rewrite that flattens
    /// `assert(a && b && ...)` into `assert(a); assert(b); ...` as a
    /// canonicalization rule, rather than special-casing it here.
    pub(crate) fn collect_and_leaves(&self, exp: &HOp<C>) -> Vec<AndLeaf<C>> {
        let mut out = Vec::new();
        self.collect_leaves(exp, None, &mut out);
        out
    }

    fn collect_leaves(&self, exp: &HOp<C>, reduction: Option<Ref>, out: &mut Vec<AndLeaf<C>>) {
        let split = self.options.split_reductions;
        let traced = |op: &GOp<C>| backend::op::mk::<C>(op.clone());
        match exp.get() {
            Op::Bin(BinOp::And, a, b, _) => {
                self.collect_leaves(a, reduction, out);
                self.collect_leaves(b, reduction, out);
            }
            Op::Ref(r, _) => match self.node_ops.get(r) {
                Some(op @ Op::Bin(BinOp::And, ..)) => {
                    self.collect_leaves(&traced(op), reduction, out);
                }
                Some(Op::Reduce(BinOp::And, v)) if split => {
                    if let ATyp::Vec(deref!(ATyp::Base(ABase::Bool)), n) = v.typ() {
                        for i in 0..n {
                            self.collect_element(v, i, reduction.or(Some(*r)), out);
                        }
                    } else {
                        out.push(AndLeaf::whole(exp, reduction));
                    }
                }
                Some(Op::ReduceMap(BinOp::And, ..)) if split && self.elements.contains_key(r) => {
                    for element in &self.elements[r] {
                        let element = Op::Ref(element.reference, element.typ.clone());
                        self.collect_leaves(&traced(&element), reduction.or(Some(*r)), out);
                    }
                }
                _ => out.push(AndLeaf::whole(exp, reduction)),
            },
            _ => out.push(AndLeaf::whole(exp, reduction)),
        }
    }

    /// Collect the leaves of element `i` of the `Vec<Bool>` expression `v`:
    /// from the element's own expression or variable when there is one, and
    /// otherwise as that element of `v`.
    fn collect_element(
        &self,
        v: &HOp<C>,
        i: usize,
        reduction: Option<Ref>,
        out: &mut Vec<AndLeaf<C>>,
    ) {
        if let Op::Ref(r, _) = v.get() {
            let element = match self.node_ops.get(r) {
                Some(Op::Vec(elements)) => elements
                    .get(i)
                    .filter(|e| matches!(e.get(), Op::Ref(..)))
                    .cloned(),
                _ => self
                    .elements
                    .get(r)
                    .and_then(|es| es.get(i))
                    .map(|e| backend::op::mk::<C>(Op::Ref(e.reference, e.typ.clone()))),
            };
            if let Some(element) = element {
                self.collect_leaves(&element, reduction, out);
                return;
            }
        }
        out.push(AndLeaf {
            exp: v.clone(),
            index: Some(i),
            reduction,
        });
    }

    /// With [`EncodeOptions::split_reductions`], remember the operation
    /// bound to `var`, so that an `&&` chain or `==` an encoding materializes
    /// into a sentinel can be traced like a graph node.
    pub(crate) fn note_op(&mut self, var: &Var, op: &GOp<C>) {
        if self.options.split_reductions {
            self.node_ops.insert(var.reference, op.clone());
        }
    }

    /// With [`EncodeOptions::split_reductions`], remember the variable bound
    /// to each element of the result `var`.
    pub(crate) fn note_elements(&mut self, var: &Var, elements: &[Var]) {
        if self.options.split_reductions {
            self.elements.insert(var.reference, elements.to_vec());
        }
    }
}

impl<C: ArkConfig> AndLeaf<C> {
    fn whole(exp: &HOp<C>, reduction: Option<Ref>) -> Self {
        Self {
            exp: exp.clone(),
            index: None,
            reduction,
        }
    }
}

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    pub(crate) fn add_op(&mut self, var: Var, op: GOp<C>, ideal: &mut Ideal<C>) {
        let mut ctx = EncodeCtx {
            builder: self,
            ideal,
        };
        match op {
            Op::Ref(r, typ) => {
                if var.reference == r && var.index.is_empty() && var.typ == typ {
                    return;
                }

                let ref_src: PolySource<C> =
                    PolySource::from_ref_vars(&ctx.ideal.vars, &Op::Ref(r, typ.clone()));
                let lifted = ref_src.lift_to(&var.typ);
                link_to_polys(ctx.ideal, &var, lifted.polys);
            }
            Op::Bin(BinOp::Add, a, b, _) => {
                ops::addsub::add_op(&mut ctx, &var, &a, &b, &var.typ);
            }
            Op::Bin(BinOp::Sub, a, b, _) => {
                ops::addsub::sub_op(&mut ctx, &var, &a, &b, &var.typ);
            }
            Op::Bin(BinOp::Mul, ref a, ref b, _) => {
                ops::mul::mul_op(&mut ctx, &var, a, b, &var.typ);
            }
            // && is multiplication in the GB encoding (Bool values are 0/1)
            Op::Bin(BinOp::And, ref a, ref b, _) => {
                ops::mul::mul_op(&mut ctx, &var, a, b, &var.typ);
            }
            Op::Bin(BinOp::Dot, ref a, ref b, _) => {
                ops::dot::dot_op(&mut ctx, &var, a, b);
            }
            Op::Bin(BinOp::Div, ref a, ref b, _) => {
                ops::div::div_rem_op(&mut ctx, &var, a, b, false);
            }
            Op::Bin(BinOp::Rem, ref a, ref b, _) => {
                ops::div::div_rem_op(&mut ctx, &var, a, b, true);
            }
            Op::Assert(ref a) => ops::check::assert_op(&mut ctx, &var, a),
            Op::Verify(ref a) => ops::check::verify_op(&mut ctx, &var, a),
            Op::Bin(BinOp::Equ, ref a, ref b, _) => ops::bool::equ_op(&mut ctx, &var, a, b),
            Op::Challenge(_, _) | Op::Random(_, _) => {}
            Op::Interpolate(ref points, ref evals) => {
                ops::interpolate::interpolate_op(&mut ctx, var, points, evals);
            }
            // Op::Ifft(v): p = ifft(v) — inverse DFT. The coefficient form `var`
            // is the IDFT of the evaluation form `a`. Each coefficient is:
            //   p[j] = (1/N) · Σ_i ω^{-i·j} · v[i]
            // where ω is a primitive N-th root of unity. The type checker
            // guarantees N is a 2-adic divisor of |F|-1, so ω always exists.
            Op::Ifft(ref a) => {
                ops::fft::ifft_op(&mut ctx, &var, a);
            }
            // Op::Fft(p): v = fft(p) — forward DFT. Each evaluation is:
            //   v[i] = Σ_j ω^{i·j} · p[j]
            // The type checker guarantees N is a 2-adic divisor of |F|-1.
            Op::Fft(ref a) => {
                ops::fft::fft_op(&mut ctx, &var, a);
            }
            // Op::Poly / Op::Mle / Op::Coef / Op::ToScalar: bind the i-th Var
            // slot of `var` to the i-th scalar poly read from `inner` by
            // `ref_vars`. These share identity semantics on coefficients /
            // evaluations — only the slot-count / enumeration of `var.typ`
            // differs, and that is driven entirely by the input's shape
            // (ref_vars already returns the right number of polys). ToScalar
            // is the Fin → Scalar embedding: `ref_vars` already encodes finite
            // indices as scalar polynomials and the slot count is unchanged.
            // Basis-change between coefficient and evaluation form happens in
            // later phases (Eval / Bin on mixed polynomial types).
            Op::Poly(ref inner)
            | Op::Mle(ref inner)
            | Op::Coef(ref inner)
            | Op::ToScalar(ref inner) => {
                let polys = PolySource::ref_vars(inner, &ctx.ideal.vars);
                debug_assert!(
                    !polys.is_empty(),
                    "Op::Poly/Mle/Coef/ToScalar produced zero polys for {:?}",
                    var.typ
                );
                link_to_polys(ctx.ideal, &var, polys);
            }
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pr_i = var.with_index(i).unwrap();
                    ctx.builder.add_op(pr_i, v.get().clone(), ctx.ideal);
                }
            }
            // Op::Evaluate(p, xs): evaluate a polynomial `p` at points `xs`.
            // See `ops::eval::eval_op` for the three-shape dispatch
            // (batched, selected, full-grid DFT).
            Op::Evaluate(ref p, range, ref pts) => {
                ops::eval::eval_op(&mut ctx, &var, p, range, pts.as_deref());
            }
            Op::Map(ref domain, ref body) => {
                ops::map::map_op(&mut ctx, var, domain, body, &[], &[]);
            }
            Op::ReduceMap(rop, ref domain, ref body) => {
                ops::map::reduce_map_op(&mut ctx, var, rop, domain, body, &[], &[]);
            }
            Op::LoopParam(_, _) => ops::uncovered_op("loop-param", &var),
            // Phase 10: `Op::Reduce(op, v)` — left-fold of vector elements.
            // See `reduce_op` for per-operator handling.
            Op::Reduce(rop, ref v) => {
                ops::reduce::reduce_op(&mut ctx, &var, rop, v);
            }
            // Phase 10: `Op::Value(lit)` — pattern-match on the `Value`
            // variant via `to_poly_value`, then bind each slot of `var` to
            // the corresponding literal polynomial. This lets literal
            // constants act as real polynomials in the basis (e.g.
            // `let c = 7; verify(x == c)` folds without needing an
            // opaque `c` variable).
            //
            // Group / Pair / Poly literals aren't scalars and fall through
            // to the opaque catch-all below via `to_poly_value`'s
            // `panic!` — which we guard against with a try-convert.
            Op::Value(ref v) => {
                ops::value::value_op(&mut ctx, &var, v);
            }
            // Phase 10: `Op::Ram(a, b)` — RAM reads with a literal index `i`
            // resolve to the i-th logical element of the array. For compound
            // element types, all physical slots are linked pairwise.
            // Multi-index (VecIndex) reads produce a vector of elements.
            // Runtime indices fall back to opaque.
            Op::Ram(ref a, ref b) => {
                ops::ram::ram_op(&mut ctx, &var, a, b);
            }
            // Phase 12: `Op::Pair(a, b, t)` — bilinear pairing.
            // For each slot position, the ideal is bound to the
            // exponent-space product:
            //
            //   var(var[i]) = var(a[i]) · var(b[i])
            //
            // Matching pair expressions on both sides of a `verify(lhs == rhs)`
            // cancel under Buchberger because their basis rows are identical
            // F-polynomials.
            Op::Pair(ref a, ref b, _) => {
                ops::pair::pair_op(&mut ctx, &var, a, b);
            }
            // `Op::Record(fields)` — field-slot-aware layout.
            // For each field, get the field-level Var via `with_index`,
            // then expand its sub-slots via `slots()` to get hierarchical
            // indices (e.g. `[0][0]`, `[0][1]` for a Vec field).
            Op::Record(ref fields) => {
                ops::record::record_op(&mut ctx, &var, fields);
            }
            // Concat/Pow/Marginalize/Proj require explicit ideal treatment;
            // unsupported shapes fail instead of becoming hidden op state.
            Op::Bin(BinOp::Concat, ref a, ref b, _) => {
                ops::concat::concat_op(&mut ctx, &var, a, b);
            }
            Op::Bin(BinOp::Pow, ref a, ref b, _) => {
                ops::pow::pow_op(&mut ctx, &var, a, b);
            }
            // `Op::Proj(inner, field, typ)` — extract a field from a Record.
            // The field's physical slots sit at an offset within the Record's
            // slot layout: offset = sum of physical_len() of preceding fields
            // (in Ctx iteration order). Emit basis rows linking proj ideal
            // slots to the corresponding inner Record slots.
            //
            // Non-record inner types are not supported — after IR lowering every
            // Proj must operate on a Record; any other variant is a compiler bug.
            Op::Proj(ref inner, ref field, ref _typ) => {
                ops::record::proj_op(&mut ctx, &var, inner, field);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::frontend::Polynomial;

    use backend::ArkBls12_381;
    use backend::Value;

    use backend::op::mk;

    // -----------------------------------------------------------------
    // add_op: Op::Poly / Op::Mle / Op::Coef (identity on coefficient slots)
    // -----------------------------------------------------------------

    #[test]
    fn test_add_op_poly_binds_coefficient_slots() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // First: bind Vec of scalars on node 0, then Poly on node 1.
        let var_v = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 2), Qualifier::Witness);
        ideal.register(&var_v);
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_v.clone(), Op::Vec(coefs), &mut ideal);

        let var_p = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 2), Qualifier::Witness);
        let op_poly: GOp<ArkBls12_381> = Op::Poly(mk::<ArkBls12_381>(Op::Ref(
            graph::Ref::new(NodeIndex::new(0)),
            ATyp::VPoly(1, 2),
        )));
        ideal.register(&var_p);
        builder.add_op(var_p.clone(), op_poly, &mut ideal);

        // Three coefficient slots should have been bound.
        for i in 0..3 {
            let slot = var_p.clone().with_index(i).unwrap();
            assert!(ideal.pl.contains(&slot), "slot {} missing from pl", i);
        }
        // Six basis equations: 3 from Vec binding + 3 from Poly identity.
        assert_eq!(ideal.generating_set.len(), 6);
    }

    #[test]
    fn test_add_op_coef_roundtrips_poly() {
        // Op::Coef(Op::Poly(v)) bound to the same slots should reduce to `v`.
        use crate::Var;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // First: bind Vec of scalars on node 0, then Poly on node 1.
        let var_v = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 2), Qualifier::Witness);
        ideal.register(&var_v);
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_v.clone(), Op::Vec(coefs), &mut ideal);

        // Poly: reads the Vec's slots via Ref.
        let var_p = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 2), Qualifier::Witness);
        ideal.register(&var_p);
        builder.add_op(
            var_p.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(1, 2),
            ))),
            &mut ideal,
        );

        // Then: Op::Coef reading the VPoly back into a Uni(2) output
        // (degree 2 = 3 coefficient slots, per docs/poly-encoding.md).
        let var_c = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Witness);
        let ref_p: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 2));
        builder.add_op(
            var_c.clone(),
            Op::Coef(mk::<ArkBls12_381>(ref_p)),
            &mut ideal,
        );

        // Each Coef slot should be bound identically to the corresponding
        // VPoly coefficient Var — that's the round-trip identity. `ref_vars`
        // resolves per-slot Vars to ATyp::scalar(), so we expect that form
        // on the RHS.
        for i in 0..3 {
            let coef_slot = var_c.clone().with_index(i).unwrap();
            let poly_slot = var_p.clone().with_index(i).unwrap();
            let stored = ideal.pl.get(&coef_slot).expect("coef slot missing");
            let expected = Polynomial::<Fr>::var(&poly_slot);
            assert_eq!(*stored, expected, "coef[{}] did not bind to poly[{}]", i, i);
        }
    }

    #[test]
    fn test_add_op_mle_binds_hypercube_slots() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // First: bind Vec of scalars on node 0, then Mle on node 1.
        let var_v = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Witness);
        ideal.register(&var_v);
        let vals: Vec<_> = (1..=4u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_v.clone(), Op::Vec(vals), &mut ideal);

        let var_m = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Witness);
        ideal.register(&var_m);
        builder.add_op(
            var_m.clone(),
            Op::Mle(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(2),
            ))),
            &mut ideal,
        );

        // 4 from Vec binding + 4 from Mle identity.
        assert_eq!(ideal.generating_set.len(), 8);
        for i in 0..4 {
            assert!(
                ideal.pl.contains(&var_m.clone().with_index(i).unwrap()),
                "mle slot {} missing",
                i
            );
        }
    }

    // -----------------------------------------------------------------
    // add_op: Op::Challenge / Op::Random (no-op in ideal)
    // -----------------------------------------------------------------

    /// Test that challenge emits no basis or pl state.

    #[test]
    fn challenge_emits_no_basis_or_pl_state() {
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(100), ATyp::scalar(), Qualifier::Instance);

        builder.add_op(
            var.clone(),
            Op::Challenge(ATyp::scalar(), false),
            &mut ideal,
        );

        assert!(
            ideal.generating_set.is_empty(),
            "challenge should not emit basis polynomials"
        );
        assert!(
            !ideal.pl.contains(&var),
            "challenge should not insert into pl"
        );
        assert!(
            !ideal.vars().contains(&var),
            "challenge should not be visible in vars() unless used in a polynomial"
        );
    }

    /// Test that random emits no basis or pl state.

    #[test]
    fn random_emits_no_basis_or_pl_state() {
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(101), ATyp::scalar(), Qualifier::Witness);

        builder.add_op(var.clone(), Op::Random(ATyp::scalar(), false), &mut ideal);

        assert!(
            ideal.generating_set.is_empty(),
            "random should not emit basis polynomials"
        );
        assert!(!ideal.pl.contains(&var), "random should not insert into pl");
        assert!(
            !ideal.vars().contains(&var),
            "random should not be visible in vars() unless used in a polynomial"
        );
    }

    /// Test that a challenge used in a polynomial is visible through basis.vars().
    /// This test captures the desired invariant: challenges become visible when referenced.

    #[test]
    fn challenge_used_in_polynomial_is_visible() {
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // Create a challenge Var
        let challenge_var =
            Var::from_node(NodeIndex::new(200), ATyp::scalar(), Qualifier::Instance);
        ideal.register(&challenge_var);
        builder.add_op(
            challenge_var.clone(),
            Op::Challenge(ATyp::scalar(), false),
            &mut ideal,
        );

        // Create a witness variable
        let x_var = Var::from_node(NodeIndex::new(201), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&x_var);

        // Create a polynomial operation that uses the challenge: y = x + c
        let y_var = Var::from_node(NodeIndex::new(202), ATyp::scalar(), Qualifier::Instance);
        ideal.register(&y_var);

        builder.add_op(
            y_var.clone(),
            Op::Bin(
                lang::ast::BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(201)),
                    ATyp::scalar(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(200)),
                    ATyp::scalar(),
                )),
                ATyp::scalar(),
            ),
            &mut ideal,
        );

        // The challenge should now be visible through basis.vars() and ideal.vars()
        let basis_vars = ideal
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        assert!(
            basis_vars.contains(&challenge_var),
            "challenge must be visible through basis vars once an equation references it"
        );
        assert!(
            ideal.vars().contains(&challenge_var),
            "challenge must be in ideal.vars() when used in polynomial"
        );
    }

    /// Test that Op::Pair emits a basis row binding the ideal to a*b
    /// without any GT sentinel variable.

    #[test]
    fn pair_emits_product_without_sentinel() {
        use backend::op::mk;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let g1_var = Var::from_node(NodeIndex::new(300), ATyp::g1(), Qualifier::Instance);
        ideal.register(&g1_var);

        let g2_var = Var::from_node(NodeIndex::new(301), ATyp::g2(), Qualifier::Instance);
        ideal.register(&g2_var);

        let pair_ideal_var = Var::from_node(NodeIndex::new(302), ATyp::gt(), Qualifier::Instance);
        ideal.register(&pair_ideal_var);

        builder.add_op(
            pair_ideal_var.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(300)), ATyp::g1())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(301)), ATyp::g2())),
                ATyp::gt(),
            ),
            &mut ideal,
        );

        // The basis should contain a row: pair_ideal - g1*g2 = 0
        // (no GT sentinel variable)
        let basis_vars = ideal
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        assert!(
            basis_vars.contains(&g1_var),
            "g1 must be visible through basis vars"
        );
        assert!(
            basis_vars.contains(&g2_var),
            "g2 must be visible through basis vars"
        );
        assert!(
            basis_vars.contains(&pair_ideal_var),
            "pair ideal must be visible through basis vars"
        );
        // No GT sentinel should exist
        let has_gt_sentinel = basis_vars
            .iter()
            .any(|var| var.name.starts_with("__zippel::gb::gt"));
        assert!(!has_gt_sentinel, "GT sentinel should not exist");
    }
}
