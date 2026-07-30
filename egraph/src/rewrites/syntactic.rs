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
