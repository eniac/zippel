//! RAM read op encoder: `ram_op`.

use backend::op::HasOpFactory;
use backend::{ArkConfig, Value};
use graph::{HOp, Op};

use crate::Var;

use super::EncodeCtx;
use super::link_to_witness;

/// Encode `Op::Ram(a, b)`: RAM reads with a literal index `i` resolve
/// to the i-th logical element of the array. For compound element types,
/// all physical slots are linked pairwise. Multi-index (VecIndex) reads
/// produce a vector of elements. Runtime indices are unsupported.
pub fn ram_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
) {
    match b.get() {
        Op::Value(Value::Index(i)) => {
            let Op::Ref(r, _) = a.get() else {
                panic!(
                    "Ram array operand must be Ref; got {:?}",
                    std::mem::discriminant(a.get())
                )
            };
            let array_var = ctx.ideal.find_ref(r);
            let Some(elem_var) = array_var.with_index(*i) else {
                panic!(
                    "Ram operand with literal index must be within bound; Got {:?}",
                    *i
                )
            };

            link_to_witness(ctx.ideal, var, &elem_var);
        }
        Op::Value(Value::VecIndex(vs)) => {
            let Op::Ref(r, _) = a.get() else {
                panic!(
                    "Ram array operand must be Ref; got {:?}",
                    std::mem::discriminant(a.get())
                )
            };
            let array_var = ctx.ideal.find_ref(r);
            for (j, idx) in vs.iter().enumerate() {
                let src_var = array_var.with_index(*idx).unwrap();
                let dst_var = var.with_index(j).unwrap();
                link_to_witness(ctx.ideal, &dst_var, &src_var);
            }
        }
        _ => {
            panic!(
                "ideal: operation has no polynomial-ideal treatment at dynamic-ram for {}",
                var.verbose()
            );
        }
    }
}
