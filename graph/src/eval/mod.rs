pub mod error;

use crate::{HOp, Ref, Op};
use backend::{ArkConfig, Value};
use backend::op::HasOpFactory;
use lang::ast::BinOp;
use error::EvalError;
use std::collections::HashMap;

/// Evaluate an Op expression given an environment mapping references to values
pub fn eval_op<C: HasOpFactory>(
    op: &HOp<C>,
    env: &HashMap<Ref, Value<C>>
) -> Result<Value<C>, EvalError> {
    match &**op {
        Op::Value(v) => Ok(v.clone()),
        Op::Ref(r, _) => eval_ref_inner(r, env),
        Op::Bin(binop, a, b, _) => {
            let va = eval_op(a, env)?;
            let vb = eval_op(b, env)?;
            match binop {
                BinOp::Add => Ok(va + vb),
                BinOp::Sub => Ok(va - vb),
                BinOp::Mul => Ok(va * vb),
                _ => Err(EvalError::ValueError("Unsupported binary op".to_string()))
            }
        }
        _ => Err(EvalError::ValueError("Unsupported op".to_string()))
    }
}

/// Evaluate a reference by looking it up in the environment
fn eval_ref_inner<C: ArkConfig>(
    r: &Ref,
    env: &HashMap<Ref, Value<C>>
) -> Result<Value<C>, EvalError> {
    env.get(r)
        .cloned()
        .ok_or_else(|| EvalError::UndefinedRef(r.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBn254;
    use crate::mk;
    
    type Fr = <ArkBn254 as ArkConfig>::F;
    type TestValue = Value<ArkBn254>;
    
    #[test]
    fn test_eval_value() {
        let op = mk::<ArkBn254>(Op::Value(TestValue::Scalar(Fr::from(42))));
        let env = HashMap::new();
        let result = eval_op(&op, &env).unwrap();
        assert_eq!(result, TestValue::Scalar(Fr::from(42)));
    }
    
    // TODO: Add more comprehensive tests once we have proper constructors
    // For now, the basic infrastructure is tested above
}
