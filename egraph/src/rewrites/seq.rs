//! Seq-elimination rewrite (ix).
//!
//! `(seq ?first ?second)` → `?second` when
//! `!egraph[?first].data.has_visible_side_effect`.

use super::{pat, v};
use crate::lang::{ZAnalysis, ZIR};
use backend::ArkConfig;
use egg::{ConditionalApplier, ENodeOrVar, Id, Rewrite, Subst, Var};

/// Condition: ?first has no visible side effect.
struct NoVisibleSideEffect {
    first: Var,
}

impl<C: ArkConfig + std::fmt::Debug> egg::Condition<ZIR<C>, ZAnalysis<C>> for NoVisibleSideEffect {
    fn check(
        &self,
        egraph: &mut egg::EGraph<ZIR<C>, ZAnalysis<C>>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        let id = *subst.get(self.first).expect("var bound");
        !egraph[id].data.has_visible_side_effect
    }
}

pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    vec![
        // Seq(?first, ?second) → ?second  when !has_visible_side_effect(?first)
        Rewrite::new(
            "seq-eliminate",
            pat(vec![
                ENodeOrVar::Var(v("?first")),
                ENodeOrVar::Var(v("?second")),
                ENodeOrVar::ENode(ZIR::Seq([Id::from(0), Id::from(1)])),
            ]),
            ConditionalApplier {
                condition: NoVisibleSideEffect { first: v("?first") },
                applier: pat(vec![ENodeOrVar::Var(v("?second"))]),
            },
        )
        .unwrap(),
    ]
}

#[cfg(test)]
mod tests {
    use backend::{ArkBls12_381, Value};
    use egg::{EGraph, Symbol};

    use super::super::test_utils::{ZEgraph, saturate};
    use crate::lang::ZIR;

    #[test]
    fn test_seq_eliminate_no_side_effect() {
        let mut eg: ZEgraph = EGraph::default();
        let first = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        )));
        let second = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let seq = eg.add(ZIR::Seq([first, second]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(seq),
            eg.find(second),
            "seq-eliminate should unify Seq(no-side-effect, second) with second"
        );
    }

    #[test]
    fn test_seq_eliminate_with_random() {
        let mut eg: ZEgraph = EGraph::default();
        let random = eg.add(ZIR::Random(Symbol::from("r1"), false));
        let second = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let seq = eg.add(ZIR::Seq([random, second]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(seq),
            eg.find(second),
            "seq-eliminate should eliminate Seq with Random first (not visible side effect)"
        );
    }

    #[test]
    fn test_seq_not_eliminated_with_challenge() {
        let mut eg: ZEgraph = EGraph::default();
        let challenge = eg.add(ZIR::Challenge(Symbol::from("c1"), false));
        let second = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let seq = eg.add(ZIR::Seq([challenge, second]));

        saturate(&mut eg);

        assert_ne!(
            eg.find(seq),
            eg.find(second),
            "seq-eliminate should NOT eliminate Seq with Challenge first (visible side effect)"
        );
    }
}
