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
