//! `PolySource`: an owned slice of polynomial variables paired with
//! their `ATyp`. Provides element-wise access for `Vec` types (via
//! `at_index`), zero-padding lifts to wider types (via `lift_to`),
//! all-slot scalar broadcast (via `broadcast_scalar_to`), and
//! representation-aware scalar lifting for additive polynomial
//! operations.

use std::collections::HashMap;

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps, Value};
use graph::{GOp, Op, Ref};

use crate::Var;
use crate::frontend::Polynomial;

use super::combinatorics::{hypercube, multi_indices};

/// An owned slice of polynomial variables paired with their `ATyp`.
///
/// Provides element-wise access for `Vec` types (via `at_index`),
/// zero-padding lifts to wider types (via `lift_to`), all-slot scalar
/// broadcast (via `broadcast_scalar_to`), and representation-aware
/// scalar lifting for additive polynomial operations.
pub struct PolySource<C: ArkConfig> {
    pub polys: Vec<Polynomial<C::F>>,
    pub typ: ATyp,
}

impl<C: ArkConfig> PolySource<C> {
    pub fn new(polys: Vec<Polynomial<C::F>>, typ: ATyp) -> Self {
        PolySource { polys, typ }
    }

    pub fn typ(&self) -> &ATyp {
        &self.typ
    }

    pub fn polys(&self) -> &[Polynomial<C::F>] {
        &self.polys
    }

    pub fn from_ref_vars(vars: &HashMap<Ref, Var>, op: &GOp<C>) -> Self
    where
        C: HasOpFactory,
    {
        let typ = op.typ();
        let polys = Self::ref_vars(op, vars);
        PolySource { polys, typ }
    }

    pub fn from_vars(var: &Var, typ: ATyp) -> Self {
        let polys = var
            .slots()
            .into_iter()
            .map(|slot| Polynomial::var(&slot))
            .collect();
        PolySource { polys, typ }
    }

    fn embed_multi_indexed_polys(
        polys: &[Polynomial<C::F>],
        source_indices: &[Vec<usize>],
        target_indices: &[Vec<usize>],
        target_arity: usize,
    ) -> Vec<Polynomial<C::F>> {
        let mut out = vec![Polynomial::<C::F>::zero(); target_indices.len()];
        for (j, source_index) in source_indices.iter().enumerate() {
            let mut padded = source_index.clone();
            padded.resize(target_arity, 0);
            if let Some(target_slot) = target_indices.iter().position(|target| target == &padded) {
                out[target_slot] = polys[j].clone();
            }
        }
        out
    }

    pub fn at_index(&self, i: usize) -> Option<PolySource<C>> {
        match &self.typ {
            ATyp::Vec(inner, n) if i < *n => {
                let elem_len = inner.physical_len();
                Some(PolySource {
                    polys: self.polys[i * elem_len..(i + 1) * elem_len].to_vec(),
                    typ: (**inner).clone(),
                })
            }
            _ => None,
        }
    }

    /// Lift polys from `self.typ` to `target`, producing a `PolySource`
    /// with exactly `target.physical_len()` polys.
    ///
    /// Only handles type combinations permitted by `lub_equ`, `lub_add`,
    /// and `lub_sub`. Panics on any other combination — the type checker
    /// guarantees these never occur.
    ///
    /// # Correctness guarantees
    ///
    /// **Base → Base**: same slot count, identity mapping.
    ///
    /// **Uni(n) → Uni(n')** where `n ≤ n'`:
    ///   Uni(n) = VPoly(1,n) has `n+1` slots in graded-lex order.
    ///   `multi_indices(1, n)` is a prefix of `multi_indices(1, n')`,
    ///   so zero-padding is correct.
    ///
    /// **VPoly(n, m) → VPoly(n, m')** where `m ≤ m'` (same arity, wider degree):
    ///   `multi_indices(n, m)` is a prefix of `multi_indices(n, m')` because
    ///   graded-lex enumerates by total degree first; all indices with `|k| ≤ m`
    ///   appear before any with `|k| = m+1`. Zero-padding is correct.
    ///
    /// **VPoly(n1, m1) → VPoly(n2, m2)** where `n1 < n2` and `m1 ≤ m2`:
    ///   NOT a simple prefix. Each source multi-index `(k1,…,kn1)` embeds as
    ///   `(k1,…,kn1,0,…,0)` in `n2`-variable space. We look up each embedded
    ///   index's position in `multi_indices(n2, m2)` and place the source poly
    ///   there; all other ideal slots are zero.
    ///
    /// **Mle(n1) → Mle(n2)** where `n1 ≤ n2`:
    ///   The hypercube `{0,1}^n1` embeds as `{(b1,…,bn1,0,…,0)} ⊂ {0,1}^n2`.
    ///   Since `hypercube` enumerates in bit-order, each `(b1,…,bn1)` maps to
    ///   the same slot index in Mle(n2) (trailing zeros don't affect the index).
    ///   Mle(n1) IS a prefix of Mle(n2) — zero-padding is correct.
    ///
    /// **Mle(n) → VPoly(n', m')** where `n ≤ n'`:
    ///   Cross-type lift (from `lub_add`/`lub_sub` when Mle arities differ).
    ///   Mle stores evaluations at hypercube points; VPoly stores coefficients
    ///   at multi-indices. We convert via Lagrange-basis expansion: the VPoly
    ///   coefficient at multi-index `k` is `Σ_b f(b) · Π_i C[b_i][k_i]`
    ///   where `C = [[1,-1],[0,1]]` encodes `L_0(x)=1-x`, `L_1(x)=x`.
    ///
    /// **Uni(n) → VPoly(n', m')** where `1 ≤ n'` and `n ≤ m'`:
    ///   Same as VPoly(1,n) → VPoly(n',m'). Handled by same-arity prefix or
    ///   cross-arity embedding as above.
    pub fn lift_to(&self, target: &ATyp) -> PolySource<C> {
        let src_len = self.typ.physical_len();
        let dst_len = target.physical_len();
        assert!(
            src_len <= dst_len,
            "lift_to: cannot lift from wider type {} ({} slots) to narrower type {} ({} slots)",
            self.typ,
            src_len,
            target,
            dst_len
        );

        if self.typ == *target {
            return PolySource {
                polys: self.polys.clone(),
                typ: target.clone(),
            };
        }

        match (&self.typ, target) {
            (ATyp::Base(_), ATyp::Base(_)) => PolySource {
                polys: self.polys.clone(),
                typ: target.clone(),
            },

            (ATyp::Uni(_n1), ATyp::Uni(_n2)) => {
                let mut out = self.polys.clone();
                out.resize(dst_len, Polynomial::zero());
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::Mle(_n1), ATyp::Mle(_n2)) => {
                let mut out = self.polys.clone();
                out.resize(dst_len, Polynomial::zero());
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::Mle(1), ATyp::Uni(m2)) if *m2 >= 1 => {
                assert_eq!(
                    self.polys.len(),
                    2,
                    "lift_to: Mle(1) source must have exactly two evaluation slots"
                );
                let g0 = self.polys[0].clone();
                let g1 = self.polys[1].clone();
                let mut out = vec![Polynomial::<C::F>::zero(); dst_len];
                out[0] = g0.clone();
                out[1] = &g1 - &g0;
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::VPoly(n1, m1), ATyp::VPoly(n2, m2)) if n1 <= n2 && m1 <= m2 => {
                if n1 == n2 {
                    let mut out = self.polys.clone();
                    out.resize(dst_len, Polynomial::zero());
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                } else {
                    let dst_idx = multi_indices(*n2, *m2);
                    let src_idx = multi_indices(*n1, *m1);
                    let out = Self::embed_multi_indexed_polys(&self.polys, &src_idx, &dst_idx, *n2);
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                }
            }

            (ATyp::Uni(m1), ATyp::VPoly(n2, m2)) if *n2 >= 1 && m1 <= m2 => {
                if *n2 == 1 {
                    let mut out = self.polys.clone();
                    out.resize(dst_len, Polynomial::zero());
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                } else {
                    let dst_idx = multi_indices(*n2, *m2);
                    let src_idx = multi_indices(1, *m1);
                    let out = Self::embed_multi_indexed_polys(&self.polys, &src_idx, &dst_idx, *n2);
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                }
            }

            // Mle(n1) → VPoly(n2, m2): convert from evaluation form to
            // coefficient form via Lagrange-basis expansion.
            //
            // Each Mle slot `j` (corresponding to hypercube point `b =
            // (b1,…,b_n1)`) stores the evaluation `f(b)`. The Lagrange
            // basis polynomial `L_b(X)` satisfies `L_b(b') = δ_{b,b'}`.
            // In coefficient form, per variable: `L_0(x) = 1-x` has
            // coefficients `[1, -1]` and `L_1(x) = x` has coefficients
            // `[0, 1]`. So the full `L_b(X) = Π_i L_{b_i}(X_i)` has
            // coefficient at multi-index `k` equal to
            // `Π_i C[b_i][k_i]` where `C = [[1,-1],[0,1]]`.
            //
            // The VPoly coefficient at index `k` is then
            // `Σ_b f(b) · Π_i C[b_i][k_i]`.
            (ATyp::Mle(n1), ATyp::VPoly(n2, m2)) if n1 <= n2 && *m2 >= 1 => {
                // Per-variable Lagrange eval→coeff: `C[b][k]` is the
                // coefficient of `x^k` in `L_b(x)`.
                // `L_0(x) = 1 - x` → C[0] = [1, -1]
                // `L_1(x) = x`     → C[1] = [0,  1]
                const C: [[i64; 2]; 2] = [[1, -1], [0, 1]];
                let src_hcube = hypercube(*n1);
                let dst_idx = multi_indices(*n2, *m2);
                let n2_val = *n2;
                let n1_val = *n1;
                let mut out = vec![Polynomial::<C::F>::zero(); dst_idx.len()];
                let lit_of = |v: i64| -> Polynomial<C::F> {
                    if v >= 0 {
                        Polynomial::lit(&C::FOps::from_usize(v as usize))
                    } else {
                        -Polynomial::lit(&C::FOps::from_usize((-v) as usize))
                    }
                };
                for (j, src_b) in src_hcube.iter().enumerate() {
                    for (ir, k) in dst_idx.iter().enumerate() {
                        let mut scalar: i64 = 1;
                        for i in 0..n1_val {
                            let ki = if i < k.len() { k[i] } else { 0 };
                            if ki >= 2 {
                                scalar = 0;
                                break;
                            }
                            scalar *= C[src_b[i]][ki];
                        }
                        if n2_val > n1_val {
                            for i in n1_val..n2_val {
                                let ki = if i < k.len() { k[i] } else { 0 };
                                if ki != 0 {
                                    scalar = 0;
                                    break;
                                }
                            }
                        }
                        if scalar == 0 {
                            continue;
                        }
                        out[ir] = &out[ir] + &(&lit_of(scalar) * &self.polys[j]);
                    }
                }
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            _ => {
                panic!(
                    "lift_to: unsupported type combination {} → {}",
                    self.typ, target
                )
            }
        }
    }

    pub fn broadcast_scalar_to(&self, poly_typ: &ATyp) -> PolySource<C> {
        let dst_len = poly_typ.physical_len();
        let scalar_poly = self.polys[0].clone();
        PolySource {
            polys: vec![scalar_poly; dst_len],
            typ: poly_typ.clone(),
        }
    }

    pub fn inject_constant_to(&self, poly_typ: &ATyp) -> PolySource<C> {
        assert!(
            Self::is_scalar_like(&self.typ),
            "inject_constant_to requires a scalar-like source, got {}",
            self.typ
        );
        assert_eq!(
            self.polys.len(),
            1,
            "inject_constant_to requires exactly one source slot"
        );

        let scalar_poly = self.polys[0].clone();
        let polys = match poly_typ {
            ATyp::Base(_) => vec![scalar_poly],
            ATyp::Uni(_) => {
                let mut out = vec![Polynomial::<C::F>::zero(); poly_typ.physical_len()];
                out[0] = scalar_poly;
                out
            }
            ATyp::VPoly(n, m) => {
                let indices = multi_indices(*n, *m);
                let zero_slot = indices
                    .iter()
                    .position(|idx| idx.iter().all(|degree| *degree == 0))
                    .expect("VPoly multi-index enumeration must include the constant slot");
                let mut out = vec![Polynomial::<C::F>::zero(); indices.len()];
                out[zero_slot] = scalar_poly;
                out
            }
            ATyp::Mle(_) => vec![scalar_poly; poly_typ.physical_len()],
            ATyp::Vec(_, _) | ATyp::Record(_) => panic!(
                "inject_constant_to: unsupported scalar lift target {}",
                poly_typ
            ),
        };

        PolySource {
            polys,
            typ: poly_typ.clone(),
        }
    }

    pub fn is_poly(&self) -> bool {
        Self::poly_shape_static(&self.typ).is_some() || matches!(self.typ, ATyp::Mle(_))
    }

    pub fn is_scalar_like(t: &ATyp) -> bool {
        matches!(t, ATyp::Base(ABase::Scalar | ABase::Fin(_)))
    }

    pub fn poly_shape_static(t: &ATyp) -> Option<(usize, usize)> {
        match t {
            ATyp::VPoly(n, m) => Some((*n, *m)),
            ATyp::Uni(m) => Some((1, *m)),
            _ => None,
        }
    }

    /// Resolve an `Op::Ref` or `Op::Value` to a vector of polynomials.
    /// Panics on other op variants — children should be materialized to
    /// `Ref` before reaching the ideal builder.
    pub fn ref_vars(op: &GOp<C>, vars: &HashMap<Ref, Var>) -> Vec<Polynomial<C::F>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = vars
                    .get(v)
                    .unwrap_or_else(|| panic!("ideal: ref {} not found in namespace vars", v));
                debug_assert_eq!(
                    pf.typ, *typ,
                    "find_ref type mismatch: namespace has {:?} but Op::Ref says {:?}",
                    pf.typ, typ,
                );
                pf.slots()
                    .into_iter()
                    .map(|s| Polynomial::var(&s))
                    .collect()
            }
            Op::Value(v) => Self::to_poly_value(v),
            other => {
                panic!(
                    "ref_vars called with unsupported op variant: {:?} — children should be materialized to Ref",
                    std::mem::discriminant(other)
                )
            }
        }
    }

    /// Convert a literal `Value` to a vector of constant polynomials.
    pub fn to_poly_value(v: &Value<C>) -> Vec<Polynomial<C::F>> {
        match v {
            Value::Scalar(s) => vec![Polynomial::lit(s)],
            Value::Index(i) => vec![Polynomial::lit(&C::FOps::from_usize(*i))],
            Value::Unit => vec![],
            Value::Vec(v) => v.iter().flat_map(|v| Self::to_poly_value(v)).collect(),
            Value::VecScalar(v) => v.iter().map(Polynomial::lit).collect::<Vec<_>>(),
            Value::VecIndex(v) => v
                .iter()
                .map(|i| Polynomial::lit(&C::FOps::from_usize(*i)))
                .collect::<Vec<_>>(),
            _ => panic!("Unsupported value: {}", v),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::Ideal;
    use super::super::IdealBuilder;
    use super::*;
    use backend::ArkBls12_381;

    #[test]
    fn test_ideal_builder_to_poly_value_scalar() {
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::Scalar(Fr::from(42u64));
        let poly = PolySource::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_ideal_builder_to_poly_value_index() {
        use backend::Value;

        let val = Value::Index(5);
        let poly = PolySource::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_ideal_builder_to_poly_value_vec_scalar() {
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::VecScalar(vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);
        let poly = PolySource::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_ideal_builder_to_poly_value_vec_index() {
        use backend::Value;

        let val = Value::VecIndex(vec![0, 1, 2]);
        let poly = PolySource::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    // -----------------------------------------------------------------
    // ref_vars on polynomial-typed refs
    // -----------------------------------------------------------------

    #[test]
    fn test_ref_vars_vpoly_expands_coefficients() {
        use crate::Var;
        use graph::Ref;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_p = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 2), Qualifier::Private);
        ideal.register(&var_p);

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2));
        let polys = PolySource::<ArkBls12_381>::ref_vars(&op, &ideal.vars);
        assert_eq!(polys.len(), 6);
        for (i, _) in polys.iter().enumerate() {
            let expected = var_p.clone().with_index(i).unwrap();
            assert!(
                polys[i].contains(&expected),
                "coefficient poly {} does not contain expected Var (index {})",
                i,
                i
            );
        }
    }

    #[test]
    fn test_ref_vars_mle_expands_evaluations() {
        use crate::Var;
        use graph::Ref;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_p = Var::from_node(NodeIndex::new(0), ATyp::Mle(3), Qualifier::Private);
        ideal.register(&var_p);

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(3));
        let polys = PolySource::<ArkBls12_381>::ref_vars(&op, &ideal.vars);
        assert_eq!(polys.len(), 8);
    }

    /// it, returning the var for caller use. The slot type isn't important
    /// here; we only need the reference node / index to resolve.

    #[test]
    fn mle1_to_uni1_lift_converts_evals_to_coeffs() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let src = Var::from_node(NodeIndex::new(10), ATyp::Mle(1), Qualifier::Private);
        let g0 = Polynomial::<ark_bls12_381::Fr>::var(&src.clone().with_index(0).unwrap());
        let g1 = Polynomial::<ark_bls12_381::Fr>::var(&src.clone().with_index(1).unwrap());
        let lifted = PolySource::<ArkBls12_381> {
            polys: vec![g0.clone(), g1.clone()],
            typ: ATyp::Mle(1),
        }
        .lift_to(&ATyp::Uni(1));

        assert_eq!(lifted.typ, ATyp::Uni(1));
        assert_eq!(lifted.polys.len(), 2);
        assert_eq!(lifted.polys[0], g0);
        assert_eq!(lifted.polys[1], &g1 - &g0);
    }

    // -----------------------------------------------------------------
    // PolySource::lift_to tests
    // -----------------------------------------------------------------

    #[test]
    fn test_lift_uni_to_wider_uni() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.vars,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
        );
        assert_eq!(src.polys.len(), 3);

        let lifted = src.lift_to(&ATyp::Uni(4));
        assert_eq!(lifted.polys.len(), 5);
        assert_eq!(*lifted.typ(), ATyp::Uni(4));
        for i in 0..3 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&var.clone().with_index(i).unwrap())
            );
        }
        for i in 3..5 {
            assert!(
                lifted.polys[i].is_zero(),
                "padded slot {} should be zero",
                i
            );
        }
    }

    #[test]
    fn test_lift_mle_to_wider_mle() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Private);
        ideal.register(&var);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.vars,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2)),
        );
        assert_eq!(src.polys.len(), 4);

        let lifted = src.lift_to(&ATyp::Mle(3));
        assert_eq!(lifted.polys.len(), 8);
        assert_eq!(*lifted.typ(), ATyp::Mle(3));
        for i in 0..4 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&var.clone().with_index(i).unwrap())
            );
        }
        for i in 4..8 {
            assert!(
                lifted.polys[i].is_zero(),
                "padded slot {} should be zero",
                i
            );
        }
    }

    #[test]
    fn test_lift_vpoly_same_arity_prefix() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 2), Qualifier::Private);
        ideal.register(&var);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.vars,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2)),
        );

        let lifted = src.lift_to(&ATyp::VPoly(2, 3));
        assert_eq!(lifted.polys.len(), 10);
        assert_eq!(*lifted.typ(), ATyp::VPoly(2, 3));
        for i in 0..6 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&var.clone().with_index(i).unwrap())
            );
        }
        for i in 6..10 {
            assert!(
                lifted.polys[i].is_zero(),
                "padded slot {} should be zero",
                i
            );
        }
    }

    #[test]
    fn test_lift_vpoly_cross_arity_embedding() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 2), Qualifier::Private);
        ideal.register(&var);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.vars,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2)),
        );

        let lifted = src.lift_to(&ATyp::VPoly(3, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(3, 2));
        assert_eq!(lifted.polys.len(), ATyp::VPoly(3, 2).physical_len());

        let dst = multi_indices(3, 2);
        let src_idx = multi_indices(2, 2);
        for (j, sk) in src_idx.iter().enumerate() {
            let mut padded = sk.clone();
            padded.resize(3, 0);
            let pos = dst.iter().position(|dk| dk == &padded).unwrap();
            assert_eq!(
                lifted.polys[pos],
                Polynomial::var(&var.clone().with_index(j).unwrap()),
                "src multi-index {:?} → padded {:?} → dst position {} should have src slot {}",
                sk,
                padded,
                pos,
                j
            );
        }
    }

    #[test]
    fn test_lift_mle_to_vpoly_lagrange() {
        use ark_bls12_381::Fr;

        let src = PolySource::<ArkBls12_381>::new(
            vec![
                Polynomial::lit(&Fr::from(1u64)),
                Polynomial::lit(&Fr::from(2u64)),
                Polynomial::lit(&Fr::from(3u64)),
                Polynomial::lit(&Fr::from(4u64)),
            ],
            ATyp::Mle(2),
        );

        let lifted = src.lift_to(&ATyp::VPoly(2, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(2, 2));
        assert_eq!(lifted.polys.len(), 6);

        let dst = multi_indices(2, 2);
        let c: [[i64; 2]; 2] = [[1, -1], [0, 1]];
        let hcube = hypercube(2);
        let vals: Vec<i64> = vec![1, 2, 3, 4];
        for (ir, k) in dst.iter().enumerate() {
            let mut expected: i64 = 0;
            for (j, b) in hcube.iter().enumerate() {
                let mut scalar: i64 = 1;
                for i in 0..2 {
                    let ki = if i < k.len() { k[i] } else { 0 };
                    if ki >= 2 {
                        scalar = 0;
                        break;
                    }
                    scalar *= c[b[i]][ki];
                }
                expected += vals[j] * scalar;
            }
            let actual = &lifted.polys[ir];
            if expected == 0 {
                assert!(
                    actual.is_zero(),
                    "Mle→VPoly coefficient at multi-index {:?} (position {}) should be zero",
                    k,
                    ir
                );
            } else {
                let expected_poly: Polynomial<ark_bls12_381::Fr> = if expected >= 0 {
                    Polynomial::lit(&Fr::from(expected as u64))
                } else {
                    -Polynomial::lit(&Fr::from((-expected) as u64))
                };
                assert_eq!(
                    *actual, expected_poly,
                    "Mle→VPoly coefficient at multi-index {:?} (position {}) mismatch",
                    k, ir
                );
            }
        }
    }

    #[test]
    fn test_lift_uni_to_vpoly_same_arity() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.vars,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
        );
        assert_eq!(src.polys.len(), 3);

        let lifted = src.lift_to(&ATyp::VPoly(1, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(1, 2));
        assert_eq!(lifted.polys.len(), 3);
        for i in 0..3 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&var.clone().with_index(i).unwrap())
            );
        }
    }

    // -----------------------------------------------------------------
    // Op::Ref with lift_to
    // -----------------------------------------------------------------

    #[test]
    fn test_ref_lift_to_wider_type() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_src = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var_src);

        let var_dst = Var::from_node(NodeIndex::new(1), ATyp::Uni(4), Qualifier::Private);
        ideal.register(&var_dst);

        builder.add_op(
            var_dst.clone(),
            Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
            &mut ideal,
        );

        assert_eq!(var_dst.slots().len(), 5, "Uni(4) should have 5 slots");
        for j in 0..3 {
            let dst_j = var_dst.clone().with_index(j).unwrap();
            let src_j = var_src.clone().with_index(j).unwrap();
            let stored = ideal.pl.get(&dst_j).unwrap();
            assert_eq!(
                *stored,
                Polynomial::var(&src_j),
                "ref lift slot {} should map to src slot {}",
                j,
                j
            );
        }
        for j in 3..5 {
            let dst_j = var_dst.clone().with_index(j).unwrap();
            let stored = ideal.pl.get(&dst_j).unwrap();
            assert!(
                stored.is_zero(),
                "ref lift padded slot {} should be zero",
                j
            );
        }
    }

    // -----------------------------------------------------------------
    // broadcast_scalar_to
    // -----------------------------------------------------------------

    #[test]
    fn test_broadcast_scalar_to_vpoly() {
        let scalar_poly = Polynomial::<ark_bls12_381::Fr>::var(&Var::from_node(
            petgraph::graph::NodeIndex::new(0),
            ATyp::scalar(),
            lang::typ::Qualifier::Private,
        ));
        let src = PolySource::<ArkBls12_381>::new(vec![scalar_poly.clone()], ATyp::scalar());
        let broadcast = src.broadcast_scalar_to(&ATyp::VPoly(2, 2));
        assert_eq!(broadcast.polys.len(), 6);
        for (i, p) in broadcast.polys.iter().enumerate() {
            assert_eq!(*p, scalar_poly, "broadcast slot {} should be the scalar", i);
        }
    }
}
