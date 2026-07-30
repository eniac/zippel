//! ZIR → RIR 1:1 injection conversion.
//!
//! Every ZIR variant maps to the same-named RIR variant.
//! Runtime-specific ops (PowerGen, SumcheckRound) are introduced by
//! runtime rewrites (iv, vi) after conversion, never by this conversion.
//!
//! NOTE: This file, RIR, RAnalysis, and RIRCost are temporarily in the
//! egraph crate. Once egraph is fully integrated, they should be moved
//! to the runtime crate.

use egg::{EGraph, Id, Language};

use crate::lang::{RAnalysis, RIR, ZAnalysis, ZIR};
use backend::ArkConfig;

/// Convert a ZIR e-graph node (by Id) into the RIR e-graph.
/// Returns the root Id in the RIR e-graph.
pub fn convert_zir_to_rir<C: ArkConfig + std::fmt::Debug>(
    zir_egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    root: Id,
    rir_egraph: &mut EGraph<RIR<C>, RAnalysis<C>>,
) -> Id {
    // We need to recursively convert. Use a simple recursive approach
    // with memoization via a HashMap.
    use std::collections::HashMap;
    let mut memo: HashMap<Id, Id> = HashMap::new();
    convert_node(zir_egraph, root, rir_egraph, &mut memo)
}

fn convert_node<C: ArkConfig + std::fmt::Debug>(
    zir_egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    zir_id: Id,
    rir_egraph: &mut EGraph<RIR<C>, RAnalysis<C>>,
    memo: &mut std::collections::HashMap<Id, Id>,
) -> Id {
    if let Some(&rir_id) = memo.get(&zir_id) {
        return rir_id;
    }

    // Pick the first node in the e-class (extraction would be better,
    // but for 1:1 conversion any representative works)
    let enode = &zir_egraph[zir_id].nodes[0];

    // Convert children first
    let children: Vec<Id> = enode
        .children()
        .iter()
        .map(|&cid| convert_node(zir_egraph, cid, rir_egraph, memo))
        .collect();

    let rir_node = match enode {
        ZIR::Var(s) => RIR::Var(*s),
        ZIR::Constant(v) => RIR::Constant(v.clone()),
        ZIR::Add(_) => RIR::Add([children[0], children[1]]),
        ZIR::Sub(_) => RIR::Sub([children[0], children[1]]),
        ZIR::Mul(_) => RIR::Mul([children[0], children[1]]),
        ZIR::Div(_) => RIR::Div([children[0], children[1]]),
        ZIR::Rem(_) => RIR::Rem([children[0], children[1]]),
        ZIR::Pow(_) => RIR::Pow([children[0], children[1]]),
        ZIR::Dot(_) => RIR::Dot([children[0], children[1]]),
        ZIR::Concat(_) => RIR::Concat([children[0], children[1]]),
        ZIR::Neg(_) => RIR::Neg([children[0]]),
        ZIR::Pair(_) => RIR::Pair([children[0], children[1]]),
        ZIR::Random(s, nz) => RIR::Random(*s, *nz),
        ZIR::Challenge(s, nz) => RIR::Challenge(*s, *nz),
        ZIR::Log(s, _) => RIR::Log(*s, [children[0]]),
        ZIR::Poly(_) => RIR::Poly([children[0]]),
        ZIR::Coef(_) => RIR::Coef([children[0]]),
        ZIR::Mle(_) => RIR::Mle([children[0]]),
        ZIR::Fft(_) => RIR::Fft([children[0]]),
        ZIR::Ifft(_) => RIR::Ifft([children[0]]),
        ZIR::Interpolate(_) => RIR::Interpolate([children[0], children[1]]),
        ZIR::Evaluate(_) => RIR::Evaluate([children[0], children[1]]),
        ZIR::EvaluateGrid(_) => RIR::EvaluateGrid([children[0]]),
        ZIR::EvaluateSelected(_) => RIR::EvaluateSelected([children[0], children[1], children[2]]),
        ZIR::Ram(_) => RIR::Ram([children[0], children[1]]),
        ZIR::Vec(_) => RIR::Vec(children.into_boxed_slice()),
        ZIR::Record(names, _) => RIR::Record(names.clone(), children.into_boxed_slice()),
        ZIR::Proj(s, _) => RIR::Proj(*s, [children[0]]),
        ZIR::Map(s, _) => RIR::Map(*s, [children[0], children[1]]),
        ZIR::Reduce(op, _) => RIR::Reduce(*op, [children[0]]),
        ZIR::Seq(_) => RIR::Seq([children[0], children[1]]),
        ZIR::Assert(_) => RIR::Assert([children[0], children[1]]),
        ZIR::Verify(_) => RIR::Verify([children[0], children[1]]),
    };

    let rir_id = rir_egraph.add(rir_node);
    memo.insert(zir_id, rir_id);
    rir_id
}
