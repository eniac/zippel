//! Syntactic rewrites — poly shape peepholes (ii), reduce→dot (v),
//! (a/b)*b→a (viii), commute, and identity rewrites.
//!
//! See `docs/egraph-plan.md` Step 8 and `docs/egraph-design-log.md` §4.

use super::{pat, v};
use crate::lang::{ZAnalysis, ZIR};
use backend::{ABase, ATyp, ArkConfig, Value};
use egg::{ConditionalApplier, ENodeOrVar, Id, Rewrite, Subst, Var};

/// Type-guard condition: ?a is field-typed (Scalar or Fin).
struct IsFieldTyped {
    var: Var,
}

impl<C: ArkConfig + std::fmt::Debug> egg::Condition<ZIR<C>, ZAnalysis<C>> for IsFieldTyped {
    fn check(
        &self,
        egraph: &mut egg::EGraph<ZIR<C>, ZAnalysis<C>>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        let id = *subst.get(self.var).expect("var bound");
        let typ = &egraph[id].data.typ;
        matches!(typ, ATyp::Base(ABase::Scalar) | ATyp::Base(ABase::Fin(_)))
    }
}

/// Build all syntactic rewrites for ZIR.
#[allow(clippy::vec_init_then_push)]
pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    let mut rules = vec![];

    // --- ii: poly shape peepholes ---
    // (ifft (fft ?p)) → ?p
    rules.push(
        Rewrite::new(
            "ifft-fft",
            pat(vec![
                ENodeOrVar::Var(v("?p")),
                ENodeOrVar::ENode(ZIR::Fft([Id::from(0)])),
                ENodeOrVar::ENode(ZIR::Ifft([Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?p"))]),
        )
        .unwrap(),
    );

    // (fft (ifft ?v)) → ?v
    rules.push(
        Rewrite::new(
            "fft-ifft",
            pat(vec![
                ENodeOrVar::Var(v("?v")),
                ENodeOrVar::ENode(ZIR::Ifft([Id::from(0)])),
                ENodeOrVar::ENode(ZIR::Fft([Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?v"))]),
        )
        .unwrap(),
    );

    // (coef (poly ?v)) → ?v
    rules.push(
        Rewrite::new(
            "coef-poly",
            pat(vec![
                ENodeOrVar::Var(v("?v")),
                ENodeOrVar::ENode(ZIR::Poly([Id::from(0)])),
                ENodeOrVar::ENode(ZIR::Coef([Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?v"))]),
        )
        .unwrap(),
    );

    // (poly (coef ?p)) → ?p
    rules.push(
        Rewrite::new(
            "poly-coef",
            pat(vec![
                ENodeOrVar::Var(v("?p")),
                ENodeOrVar::ENode(ZIR::Coef([Id::from(0)])),
                ENodeOrVar::ENode(ZIR::Poly([Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?p"))]),
        )
        .unwrap(),
    );

    // --- viii: (* (/ ?a ?b) ?b) → ?a [field-typed] ---
    {
        let lhs = pat(vec![
            ENodeOrVar::Var(v("?a")),
            ENodeOrVar::Var(v("?b")),
            ENodeOrVar::ENode(ZIR::Div([Id::from(0), Id::from(1)])),
            ENodeOrVar::ENode(ZIR::Mul([Id::from(2), Id::from(1)])),
        ]);
        let rhs = pat(vec![ENodeOrVar::Var(v("?a"))]);
        rules.push(
            Rewrite::new(
                "mul-div-cancel",
                lhs,
                ConditionalApplier {
                    condition: IsFieldTyped { var: v("?a") },
                    applier: rhs,
                },
            )
            .unwrap(),
        );
    }

    // --- commute: (+ ?a ?b) ↔ (+ ?b ?a) ---
    rules.push(
        Rewrite::new(
            "commute-add",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::Var(v("?b")),
                ENodeOrVar::ENode(ZIR::Add([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![
                ENodeOrVar::Var(v("?b")),
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Add([Id::from(0), Id::from(1)])),
            ]),
        )
        .unwrap(),
    );

    // commute: (* ?a ?b) ↔ (* ?b ?a)
    rules.push(
        Rewrite::new(
            "commute-mul",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::Var(v("?b")),
                ENodeOrVar::ENode(ZIR::Mul([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![
                ENodeOrVar::Var(v("?b")),
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Mul([Id::from(0), Id::from(1)])),
            ]),
        )
        .unwrap(),
    );

    // --- identity rewrites (require concrete zero/one constants) ---
    identity_rewrites::<C>(&mut rules);

    rules
}

/// Identity rewrites: `(+ ?a 0)` → `?a`, `(* ?a 1)` → `?a`, `(- ?a ?a)` → `0`,
/// `(?a ^ 0)` → `1`, `(?a ^ 1)` → `?a`, `(* ?a 0)` → `0`, `(neg (neg ?a))` → `?a`.
fn identity_rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>(
    rules: &mut Vec<Rewrite<ZIR<C>, ZAnalysis<C>>>,
) {
    use ark_ff::{One, Zero};

    let zero = Value::Scalar(C::F::zero());
    let one = Value::Scalar(C::F::one());

    // (+ ?a 0) → ?a
    rules.push(
        Rewrite::new(
            "add-zero",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Constant(zero.clone())),
                ENodeOrVar::ENode(ZIR::Add([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?a"))]),
        )
        .unwrap(),
    );

    // (+ 0 ?a) → ?a
    rules.push(
        Rewrite::new(
            "add-zero-left",
            pat(vec![
                ENodeOrVar::ENode(ZIR::Constant(zero.clone())),
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Add([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?a"))]),
        )
        .unwrap(),
    );

    // (* ?a 1) → ?a
    rules.push(
        Rewrite::new(
            "mul-one",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Constant(one.clone())),
                ENodeOrVar::ENode(ZIR::Mul([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?a"))]),
        )
        .unwrap(),
    );

    // (* 1 ?a) → ?a
    rules.push(
        Rewrite::new(
            "mul-one-left",
            pat(vec![
                ENodeOrVar::ENode(ZIR::Constant(one.clone())),
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Mul([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?a"))]),
        )
        .unwrap(),
    );

    // (* ?a 0) → 0
    rules.push(
        Rewrite::new(
            "mul-zero",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Constant(zero.clone())),
                ENodeOrVar::ENode(ZIR::Mul([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::ENode(ZIR::Constant(zero.clone()))]),
        )
        .unwrap(),
    );

    // (* 0 ?a) → 0
    rules.push(
        Rewrite::new(
            "mul-zero-left",
            pat(vec![
                ENodeOrVar::ENode(ZIR::Constant(zero.clone())),
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Mul([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::ENode(ZIR::Constant(zero.clone()))]),
        )
        .unwrap(),
    );

    // (- ?a ?a) → 0
    rules.push(
        Rewrite::new(
            "sub-self",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Sub([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::ENode(ZIR::Constant(zero))]),
        )
        .unwrap(),
    );

    // (?a ^ 0) → 1  (Index(0) as exponent)
    rules.push(
        Rewrite::new(
            "pow-zero",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Constant(Value::Index(0))),
                ENodeOrVar::ENode(ZIR::Pow([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::ENode(ZIR::Constant(one.clone()))]),
        )
        .unwrap(),
    );

    // (?a ^ 1) → ?a  (Index(1) as exponent)
    rules.push(
        Rewrite::new(
            "pow-one",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Constant(Value::Index(1))),
                ENodeOrVar::ENode(ZIR::Pow([Id::from(0), Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?a"))]),
        )
        .unwrap(),
    );

    // (neg (neg ?a)) → ?a
    rules.push(
        Rewrite::new(
            "neg-neg",
            pat(vec![
                ENodeOrVar::Var(v("?a")),
                ENodeOrVar::ENode(ZIR::Neg([Id::from(0)])),
                ENodeOrVar::ENode(ZIR::Neg([Id::from(1)])),
            ]),
            pat(vec![ENodeOrVar::Var(v("?a"))]),
        )
        .unwrap(),
    );
}

#[cfg(test)]
mod tests {
    use ark_ff::{One, Zero};
    use backend::{ArkBls12_381, Value};
    use egg::EGraph;

    use super::super::test_utils::{ZEgraph, saturate};
    use crate::lang::ZIR;

    #[test]
    fn test_ifft_fft_cancellation() {
        let mut eg: ZEgraph = EGraph::default();
        let p = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let fft = eg.add(ZIR::Fft([p]));
        let ifft = eg.add(ZIR::Ifft([fft]));

        saturate(&mut eg);

        assert!(
            eg.find(ifft) == eg.find(p),
            "ifft(fft(p)) should be unified with p"
        );
    }

    #[test]
    fn test_fft_ifft_cancellation() {
        let mut eg: ZEgraph = EGraph::default();
        let v = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        ])));
        let ifft = eg.add(ZIR::Ifft([v]));
        let fft = eg.add(ZIR::Fft([ifft]));

        saturate(&mut eg);

        assert!(
            eg.find(fft) == eg.find(v),
            "fft(ifft(v)) should be unified with v"
        );
    }

    #[test]
    fn test_coef_poly_cancellation() {
        let mut eg: ZEgraph = EGraph::default();
        let v = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        ])));
        let poly = eg.add(ZIR::Poly([v]));
        let coef = eg.add(ZIR::Coef([poly]));

        saturate(&mut eg);

        assert!(
            eg.find(coef) == eg.find(v),
            "coef(poly(v)) should be unified with v"
        );
    }

    #[test]
    fn test_poly_coef_cancellation() {
        let mut eg: ZEgraph = EGraph::default();
        let p = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(7),
        )));
        let coef = eg.add(ZIR::Coef([p]));
        let poly = eg.add(ZIR::Poly([coef]));

        saturate(&mut eg);

        assert!(
            eg.find(poly) == eg.find(p),
            "poly(coef(p)) should be unified with p"
        );
    }

    #[test]
    fn test_commute_add() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        )));
        let b = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let add_ab = eg.add(ZIR::Add([a, b]));
        let add_ba = eg.add(ZIR::Add([b, a]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(add_ab),
            eg.find(add_ba),
            "commute-add should unify Add(a,b) with Add(b,a)"
        );
    }

    #[test]
    fn test_commute_mul() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(3),
        )));
        let b = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(5),
        )));
        let mul_ab = eg.add(ZIR::Mul([a, b]));
        let mul_ba = eg.add(ZIR::Mul([b, a]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(mul_ab),
            eg.find(mul_ba),
            "commute-mul should unify Mul(a,b) with Mul(b,a)"
        );
    }

    #[test]
    fn test_add_zero() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let zero = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::zero(),
        )));
        let add_zero = eg.add(ZIR::Add([a, zero]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(add_zero),
            eg.find(a),
            "add-zero should unify Add(a, 0) with a"
        );
    }

    #[test]
    fn test_mul_one() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let one = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::one(),
        )));
        let mul_one = eg.add(ZIR::Mul([a, one]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(mul_one),
            eg.find(a),
            "mul-one should unify Mul(a, 1) with a"
        );
    }

    #[test]
    fn test_mul_zero() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let zero = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::zero(),
        )));
        let mul_zero = eg.add(ZIR::Mul([a, zero]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(mul_zero),
            eg.find(zero),
            "mul-zero should unify Mul(a, 0) with 0"
        );
    }

    #[test]
    fn test_mul_div_cancel() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(6),
        )));
        let b = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let div = eg.add(ZIR::Div([a, b]));
        let mul = eg.add(ZIR::Mul([div, b]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(mul),
            eg.find(a),
            "mul-div-cancel should unify Mul(Div(a,b), b) with a"
        );
    }

    #[test]
    fn test_sub_self() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let sub = eg.add(ZIR::Sub([a, a]));

        saturate(&mut eg);

        let zero_class = &eg[eg.find(sub)];
        let has_zero = zero_class.nodes.iter().any(|n| {
            matches!(n, ZIR::Constant(Value::Scalar(v)) if v == &<ArkBls12_381 as backend::ArkConfig>::F::zero())
        });
        assert!(has_zero, "sub-self should produce a zero constant");
    }

    #[test]
    fn test_neg_neg() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let neg1 = eg.add(ZIR::Neg([a]));
        let neg2 = eg.add(ZIR::Neg([neg1]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(neg2),
            eg.find(a),
            "neg-neg should unify (neg (neg a)) with a"
        );
    }
}
