use crate::TransClos;
use crate::Var;
use graph::{GOp, HOp, Op, Ref};
use lang::ast::BinOp;
use share::Ctx;
use std::collections::HashMap;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, Value};

mod combinatorics;

mod namespace;
pub use namespace::{GB_GENERATED_NAME_PREFIX, IdealNamespace};

mod ideal;
pub use ideal::Ideal;

mod poly_source;
pub(crate) use poly_source::PolySource;

mod ops;
use ops::{EncodeCtx, link_to_polys};

/// Constructs `Ideal`s from `TransClos` inputs. Owns a
/// `IdealNamespace` for division-witness and sentinel allocation
/// that persists across `build()` calls. Each call to `build(TransClos)`
/// returns a fresh `Ideal` with its own `vars` namespace.
#[derive(Clone)]
pub struct IdealBuilder<C: ArkConfig> {
    pub ns: IdealNamespace<C>,
    /// Map from Ref to the GOp that produced it, for tracing `&&` chains
    /// in assert/verify operands back to their leaf bools.
    node_ops: HashMap<Ref, GOp<C>>,
}

impl<C: ArkConfig + HasOpFactory> Default for IdealBuilder<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    pub fn new() -> Self {
        Self {
            ns: IdealNamespace::new(),
            node_ops: HashMap::new(),
        }
    }

    /// Build a `Ideal` from a `TransClos`. Each call returns a
    /// fresh ideal with its own `vars` namespace, while the builder
    /// namespace keeps generated witness/sentinel allocation stable.
    pub fn build(&mut self, tc: TransClos<C>) -> Ideal<C> {
        self.build_with_partial(tc, &Ctx::new())
    }

    /// Like [`build`](Self::build), but concretizes args whose `Ref`
    /// appears in `partial_values`. Each matching arg is constrained to
    /// known constants via [`constrain_partial_value`](Self::constrain_partial_value).
    pub fn build_with_partial(
        &mut self,
        tc: TransClos<C>,
        partial_values: &Ctx<Ref, Value<C>>,
    ) -> Ideal<C> {
        let mut ideal = Ideal::new();
        for new_arg in tc.vars.iter() {
            ideal.register(new_arg);
        }
        for (var, _op) in tc.clos.iter() {
            ideal.register(var);
        }

        // Constrain args with known partial values.
        for arg in tc.vars.iter() {
            if let Some(value) = partial_values.get(&arg.reference) {
                Self::constrain_partial_value(&mut ideal, arg, value);
            }
        }

        // Build Ref → GOp map for tracing && chains in assert/verify.
        for (var, op) in tc.clos.iter() {
            self.node_ops.insert(var.reference, op.clone());
        }

        for (var, op) in tc.clos.into_iter() {
            self.add_op(var.clone(), op, &mut ideal);
            ideal.var_order.push(var);
        }
        ideal
    }

    /// Constrain an arg variable to a known partial value.
    ///
    /// This is distinct from `PolySource::to_poly_value` (which encodes
    /// literal `Op::Value` constants into the ideal). Partial value
    /// constraining is about pinning a formal variable to a known value.
    ///
    /// **Contract**: The caller must provide the value in a form that
    /// matches the arg's type:
    /// - **Scalar-typed args** (Scalar, Fin, VecScalar, VecIndex): provide
    ///   the scalar value directly as `Value::Scalar` / `Value::VecScalar` /
    ///   `Value::Index` / `Value::VecIndex`.
    /// - **Group-typed args** (G1, G2, GT, VecG1, etc.): provide the
    ///   **discrete-log scalar** as `Value::Scalar` (or `Value::VecScalar`
    ///   for vector-typed group args). The where-clause constraints (e.g.
    ///   `alpha_g1 == alpha * gen_g1`) then propagate the scalar to the
    ///   group element's formal variable.
    ///
    /// For both cases, the value is converted to constant polynomials via
    /// `to_poly_value` and bound to the arg's slots via `link_to_polys`.
    fn constrain_partial_value(ideal: &mut Ideal<C>, arg: &Var, value: &Value<C>) {
        let polys = PolySource::<C>::to_poly_value(value);
        link_to_polys(ideal, arg, polys);
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
    /// TODO(egg): This is a manual, ad-hoc peeling of `&&` chains to avoid
    /// high-degree product polynomials in the GB generating set. Once the
    /// planned `egg`-based optimization layer is in place (see upstream PR),
    /// this should be replaced by a proper e-graph rewrite that flattens
    /// `assert(a && b && ...)` into `assert(a); assert(b); ...` as a
    /// canonicalization rule, rather than special-casing it here.
    pub(crate) fn collect_and_leaves(&self, exp: &HOp<C>) -> Vec<HOp<C>> {
        fn collect<C: ArkConfig + HasOpFactory>(
            builder: &IdealBuilder<C>,
            exp: &HOp<C>,
            out: &mut Vec<HOp<C>>,
        ) {
            match exp.get() {
                Op::Bin(BinOp::And, a, b, _) => {
                    collect(builder, a, out);
                    collect(builder, b, out);
                }
                Op::Ref(r, _) => {
                    if let Some(op) = builder.node_ops.get(r)
                        && matches!(op, Op::Bin(BinOp::And, ..))
                    {
                        let hop = backend::op::mk::<C>(op.clone());
                        collect(builder, &hop, out);
                        return;
                    }
                    out.push(exp.clone());
                }
                _ => out.push(exp.clone()),
            }
        }
        let mut out = Vec::new();
        collect(self, exp, &mut out);
        out
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
            // Op::Poly / Op::Mle / Op::Coef: bind the i-th Var slot of `var`
            // to the i-th scalar poly read from `inner` by `ref_vars`. These
            // three share identity semantics on coefficients / evaluations —
            // only the slot-count / enumeration of `var.typ` differs, and that
            // is driven entirely by the input's shape (ref_vars already returns
            // the right number of polys). Basis-change between coefficient
            // and evaluation form happens in later phases (Eval / Bin on
            // mixed polynomial types).
            Op::Poly(ref inner) | Op::Mle(ref inner) | Op::Coef(ref inner) => {
                let polys = PolySource::ref_vars(inner, &ctx.ideal.vars);
                debug_assert!(
                    !polys.is_empty(),
                    "Op::Poly/Mle/Coef produced zero polys for {:?}",
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
