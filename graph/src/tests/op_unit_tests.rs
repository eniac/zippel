//! Direct unit tests for uncovered Op functions
//! 
//! This module tests specific Op construction and manipulation functions
//! that are not covered by property tests.

#[cfg(test)]
mod op_construction_tests {
    use crate::{Op, GOp};
    use crate::tests::test_helpers::*;
    use backend::{ATyp, Value};
    use lang::typ::CRange;
    
    type C = TestConfig;
    
    #[test]
    fn test_poly_construction() {
        let val = GOp::<C>::value(&scalar::<C>(42));
        let poly_op = Op::poly(val);
        
        match poly_op {
            Op::Poly(inner) => {
                match &*inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Poly"),
                }
            }
            _ => panic!("Expected Poly operation"),
        }
    }
    
    #[test]
    fn test_coef_construction() {
        let val = GOp::<C>::value(&scalar::<C>(42));
        let coef_op = Op::coef(val);
        
        match coef_op {
            Op::Coef(inner) => {
                match &*inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Coef"),
                }
            }
            _ => panic!("Expected Coef operation"),
        }
    }
    
    #[test]
    fn test_mle_construction() {
        let val = GOp::<C>::value(&scalar::<C>(42));
        let mle_op = Op::mle(val);
        
        match mle_op {
            Op::Mle(inner) => {
                match &*inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Mle"),
                }
            }
            _ => panic!("Expected Mle operation"),
        }
    }
    
    #[test]
    fn test_fft_construction() {
        let val = GOp::<C>::value(&scalar::<C>(42));
        let fft_op = Op::fft(val);
        
        match fft_op {
            Op::Fft(inner) => {
                match &*inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Fft"),
                }
            }
            _ => panic!("Expected Fft operation"),
        }
    }
    
    #[test]
    fn test_ifft_construction() {
        let val = GOp::<C>::value(&scalar::<C>(42));
        let ifft_op = Op::ifft(val);
        
        match ifft_op {
            Op::Ifft(inner) => {
                match &*inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Ifft"),
                }
            }
            _ => panic!("Expected Ifft operation"),
        }
    }
    
    #[test]
    fn test_fft_ifft_cancellation() {
        // ifft(fft(x)) should return x
        let val = GOp::<C>::value(&scalar::<C>(42));
        let fft_op = Op::fft(val.clone());
        let result = Op::ifft(fft_op);
        
        // Should cancel out and return original
        match result {
            Op::Value(_) => (),
            _ => panic!("Expected FFT/IFFT to cancel"),
        }
    }
    
    #[test]
    fn test_ifft_fft_cancellation() {
        // fft(ifft(x)) should return x
        let val = GOp::<C>::value(&scalar::<C>(42));
        let ifft_op = Op::ifft(val.clone());
        let result = Op::fft(ifft_op);
        
        // Should cancel out and return original
        match result {
            Op::Value(_) => (),
            _ => panic!("Expected IFFT/FFT to cancel"),
        }
    }
    
    #[test]
    fn test_range_construction() {
        let range = CRange::new(0, 5);
        let range_op = GOp::<C>::range(range);
        
        match range_op {
            Op::Value(Value::VecIndex(v)) => {
                assert_eq!(v.len(), 5);
                assert_eq!(v, vec![0, 1, 2, 3, 4]);
            }
            _ => panic!("Expected VecIndex value"),
        }
    }
    
    #[test]
    fn test_zero_scalar() {
        let zero_op = GOp::<C>::zero(&ATyp::scalar());
        match zero_op {
            Op::Value(v) => {
                assert_eq!(v, Value::zero(&ATyp::scalar()));
            }
            _ => panic!("Expected Value"),
        }
    }
    
    #[test]
    fn test_zero_g1() {
        let zero_op = GOp::<C>::zero(&ATyp::g1());
        match zero_op {
            Op::Value(v) => {
                assert_eq!(v, Value::zero(&ATyp::g1()));
            }
            _ => panic!("Expected Value"),
        }
    }
    
    #[test]
    fn test_pad_zeroes_no_padding_needed() {
        let vec_val = GOp::<C>::vec(vec![
            Op::value(&scalar::<C>(1)),
            Op::value(&scalar::<C>(2)),
            Op::value(&scalar::<C>(3)),
        ]);
        
        // Padding to size 2 when we have 3 elements - no padding needed
        let result = Op::pad_zeroes(vec_val.clone(), 2);
        
        // Should return original since it's already >= target size
        match result {
            Op::Vec(v) => assert_eq!(v.len(), 3),
            _ => panic!("Expected Vec"),
        }
    }
    
    #[test]
    fn test_equ_both_values() {
        let v1 = GOp::<C>::value(&scalar::<C>(42));
        let v2 = GOp::<C>::value(&scalar::<C>(42));
        
        let result = Op::equ(v1, v2);
        
        // When both are values, should evaluate to Bool
        match result {
            Op::Value(Value::Bool(true)) => (),
            _ => panic!("Expected Bool(true) for equal values"),
        }
    }
    
    #[test]
    fn test_equ_different_values() {
        let v1 = GOp::<C>::value(&scalar::<C>(42));
        let v2 = GOp::<C>::value(&scalar::<C>(17));
        
        let result = Op::equ(v1, v2);
        
        // When both are different values, should evaluate to Bool(false)
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false) for different values"),
        }
    }
    
    #[test]
    fn test_and_both_values() {
        let v1 = GOp::<C>::value(&Value::Bool(true));
        let v2 = GOp::<C>::value(&Value::Bool(true));
        
        let result = Op::and(v1, v2);
        
        match result {
            Op::Value(Value::Bool(true)) => (),
            _ => panic!("Expected Bool(true)"),
        }
    }
    
    #[test]
    fn test_and_false_shortcircuit_left() {
        let v1 = GOp::<C>::value(&Value::Bool(false));
        let v2 = GOp::<C>::value(&Value::Bool(true));
        
        let result = Op::and(v1, v2);
        
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false) - short circuit"),
        }
    }
    
    #[test]
    fn test_and_false_shortcircuit_right() {
        let v1 = GOp::<C>::value(&Value::Bool(true));
        let v2 = GOp::<C>::value(&Value::Bool(false));
        
        let result = Op::and(v1, v2);
        
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false) - short circuit"),
        }
    }
    
    #[test]
    fn test_btrue() {
        let result = GOp::<C>::btrue();
        match result {
            Op::Value(Value::Bool(true)) => (),
            _ => panic!("Expected Bool(true)"),
        }
    }
    
    #[test]
    fn test_bfalse() {
        let result = GOp::<C>::bfalse();
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false)"),
        }
    }
    
    #[test]
    fn test_vec_construction() {
        let ops = vec![
            GOp::<C>::value(&scalar::<C>(1)),
            Op::value(&scalar::<C>(2)),
        ];
        
        let vec_op = Op::vec(ops);
        
        match vec_op {
            Op::Vec(v) => assert_eq!(v.len(), 2),
            _ => panic!("Expected Vec"),
        }
    }
    
    #[test]
    fn test_challenge_construction() {
        let challenge = GOp::<C>::challenge(ATyp::scalar());
        match challenge {
            Op::Challenge(typ, false) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Challenge"),
        }
    }
    
    #[test]
    fn test_random_construction() {
        let random = GOp::<C>::random(ATyp::scalar());
        match random {
            Op::Random(typ, false) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Random"),
        }
    }
    
    #[test]
    fn test_challenge_nz_construction() {
        let challenge = GOp::<C>::challenge_nz(ATyp::scalar());
        match challenge {
            Op::Challenge(typ, true) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Challenge with nonzero flag"),
        }
    }
    
    #[test]
    fn test_random_nz_construction() {
        let random = GOp::<C>::random_nz(ATyp::scalar());
        match random {
            Op::Random(typ, true) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Random with nonzero flag"),
        }
    }
    
    #[test]
    fn test_check_construction() {
        let val = GOp::<C>::value(&Value::Bool(true));
        let check = Op::check(val);
        
        match check {
            Op::Check(_) => (),
            _ => panic!("Expected Check"),
        }
    }
    
    #[test]
    fn test_eval_construction() {
        let p = GOp::<C>::value(&scalar::<C>(42));
        let x = Op::value(&scalar::<C>(3));
        
        let eval_op = Op::eval(p, x);
        
        match eval_op {
            Op::Eval(_, _) => (),
            _ => panic!("Expected Eval"),
        }
    }
    
    #[test]
    fn test_index_construction() {
        let index_op = GOp::<C>::index(42);
        match index_op {
            Op::Value(Value::Index(42)) => (),
            _ => panic!("Expected Index value"),
        }
    }
    
    #[test]
    fn test_pow_construction() {
        let base = GOp::<C>::value(&scalar::<C>(2));
        let exp = Op::value(&scalar::<C>(3));
        
        let pow_op = Op::pow(base, exp, ATyp::scalar());
        
        match pow_op {
            Op::Bin(lang::ast::BinOp::Pow, _, _, _) => (),
            _ => panic!("Expected Pow bin op"),
        }
    }
    
    #[test]
    fn test_dot_construction() {
        let v1 = GOp::<C>::vec(vec![Op::value(&scalar::<C>(1))]);
        let v2 = Op::vec(vec![Op::value(&scalar::<C>(2))]);
        
        let dot_op = Op::dot(v1, v2, ATyp::scalar());
        
        match dot_op {
            Op::Bin(lang::ast::BinOp::Dot, _, _, _) => (),
            _ => panic!("Expected Dot bin op"),
        }
    }
    
}

#[cfg(test)]
mod ref_tests {
    use crate::Ref;
    use petgraph::graph::NodeIndex;
    use lang::id::Vid;
    
    #[test]
    fn test_ref_node_extraction() {
        let node_idx = NodeIndex::new(42);
        let r = Ref::Node(node_idx);
        assert_eq!(r.node(), node_idx);
    }
    
    #[test]
    fn test_ref_var_extraction_some() {
        let vid = Vid::from("test_var");
        let node_idx = NodeIndex::new(0);
        let r = Ref::Var(vid.clone(), node_idx);
        assert_eq!(r.var(), Some(vid));
    }
    
    #[test]
    fn test_ref_var_extraction_none() {
        let node_idx = NodeIndex::new(42);
        let r = Ref::Node(node_idx);
        assert_eq!(r.var(), None);
    }
    
    #[test]
    fn test_ref_is_var_true() {
        let vid = Vid::from("test_var");
        let node_idx = NodeIndex::new(0);
        let r = Ref::Var(vid, node_idx);
        assert!(r.is_var());
    }
    
    #[test]
    fn test_ref_is_var_false() {
        let node_idx = NodeIndex::new(42);
        let r = Ref::Node(node_idx);
        assert!(!r.is_var());
    }
    
    #[test]
    fn test_ref_from_node_index() {
        let node_idx = NodeIndex::new(42);
        let r: Ref = node_idx.into();
        match r {
            Ref::Node(idx) => assert_eq!(idx, node_idx),
            _ => panic!("Expected Node ref"),
        }
    }
    
    #[test]
    fn test_ref_from_vid() {
        let vid = Vid::from("test");
        let r: Ref = (&vid).into();
        match r {
            Ref::Var(v, idx) => {
                assert_eq!(v, vid);
                assert_eq!(idx, NodeIndex::new(0));
            }
            _ => panic!("Expected Var ref"),
        }
    }
    
    #[test]
    fn test_ref_from_str() {
        let r: Ref = "test_var".into();
        match r {
            Ref::Var(v, idx) => {
                assert_eq!(v, Vid::from("test_var"));
                assert_eq!(idx, NodeIndex::new(0));
            }
            _ => panic!("Expected Var ref"),
        }
    }
}

#[cfg(test)]
mod op_additional_tests {
    use crate::{Op, GOp, mk};
    use crate::tests::test_helpers::*;
    use backend::{ATyp, Value, ABase};
    use lang::typ::CRange;
    use lang::ast::BinOp;
    
    type C = TestConfig;
    
    #[test]
    fn test_op_one_scalar() {
        let typ = ATyp::scalar();
        let one = GOp::<C>::one(&typ);
        match one {
            Op::Value(Value::Scalar(_)) => (),
            _ => panic!("Expected scalar one"),
        }
    }
    
    #[test]
    fn test_op_one_vec_scalar() {
        let typ = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let one = GOp::<C>::one(&typ);
        match one {
            Op::Value(Value::VecScalar(v)) => assert_eq!(v.len(), 3),
            _ => panic!("Expected vector of scalar ones"),
        }
    }
    
    #[test]
    fn test_op_one_fin() {
        let r = CRange::new(0, 5);
        let typ = ATyp::Base(ABase::Fin(r));
        let one = GOp::<C>::one(&typ);
        match one {
            Op::Value(Value::Index(1)) => (),
            _ => panic!("Expected index one"),
        }
    }
    
    #[test]
    fn test_op_one_vec_fin() {
        let r = CRange::new(0, 5);
        let typ = ATyp::Vec(Box::new(ATyp::Base(ABase::Fin(r))), 2);
        let one = GOp::<C>::one(&typ);
        match one {
            Op::Value(Value::VecIndex(v)) => {
                assert_eq!(v.len(), 2);
                assert_eq!(v[0], 1);
                assert_eq!(v[1], 1);
            }
            _ => panic!("Expected vector of index ones"),
        }
    }
    
    #[test]
    fn test_op_one_uni() {
        let typ = ATyp::Uni(3);
        let one = GOp::<C>::one(&typ);
        match one {
            Op::Value(Value::VecIndex(v)) => {
                assert_eq!(v.len(), 3);
                assert_eq!(v[0], 1);
                assert_eq!(v[1], 0);
                assert_eq!(v[2], 0);
            }
            _ => panic!("Expected univariate polynomial one"),
        }
    }
    
    #[test]
    fn test_op_pow_zero_exponent() {
        let base = GOp::<C>::value(&scalar::<C>(42));
        let exp = GOp::<C>::Value(Value::Index(0));
        let typ = ATyp::scalar();
        let result = Op::pow(base, exp, typ.clone());
        
        match result {
            Op::Value(_) => (),
            _ => panic!("Expected value for pow with zero exponent"),
        }
    }
    
    #[test]
    fn test_op_pow_one_exponent() {
        let base = GOp::<C>::value(&scalar::<C>(42));
        let exp = GOp::<C>::Value(Value::Index(1));
        let typ = ATyp::scalar();
        let result = Op::pow(base.clone(), exp, typ);
        
        assert_eq!(result, base);
    }
    
    #[test]
    fn test_op_pow_general() {
        let base = GOp::<C>::value(&scalar::<C>(2));
        let exp = GOp::<C>::value(&scalar::<C>(3));
        let typ = ATyp::scalar();
        let result = Op::pow(base, exp, typ.clone());
        
        match result {
            Op::Bin(BinOp::Pow, _, _, _) => (),
            _ => panic!("Expected Pow binary operation"),
        }
    }
    
    #[test]
    fn test_op_dot_values() {
        use ark_bls12_381::Fr;
        let a = GOp::<C>::Value(Value::VecScalar(vec![Fr::from(1u64), Fr::from(2u64)]));
        let b = GOp::<C>::Value(Value::VecScalar(vec![Fr::from(3u64), Fr::from(4u64)]));
        let typ = ATyp::scalar();
        let result = Op::dot(a, b, typ);
        
        match result {
            Op::Value(_) => (),
            _ => panic!("Expected value from dot product of values"),
        }
    }
    
    #[test]
    fn test_op_dot_non_values() {
        let a = GOp::<C>::Random(ATyp::scalar(), false);
        let b = GOp::<C>::Random(ATyp::scalar(), false);
        let typ = ATyp::scalar();
        let result = Op::dot(a, b, typ);
        
        match result {
            Op::Bin(BinOp::Dot, _, _, _) => (),
            _ => panic!("Expected Dot binary operation"),
        }
    }
    
    #[test]
    fn test_op_concat_vecs() {
        let v1 = GOp::<C>::vec(vec![
            Op::value(&scalar::<C>(1)),
            Op::value(&scalar::<C>(2)),
        ]);
        let v2 = GOp::<C>::vec(vec![
            Op::value(&scalar::<C>(3)),
        ]);
        let typ = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let result = Op::concat(v1, v2, typ);
        
        match result {
            Op::Vec(v) => assert_eq!(v.len(), 3),
            _ => panic!("Expected concatenated vector"),
        }
    }
    
    #[test]
    fn test_op_concat_vec_and_element() {
        let v = GOp::<C>::vec(vec![Op::value(&scalar::<C>(1))]);
        let e = GOp::<C>::value(&scalar::<C>(2));
        let typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let result = Op::concat(v, e, typ);
        
        match result {
            Op::Vec(v) => assert_eq!(v.len(), 2),
            _ => panic!("Expected concatenated vector"),
        }
    }
    
    #[test]
    fn test_op_div_by_zero_panics() {
        let a = GOp::<C>::value(&scalar::<C>(42));
        let zero = GOp::<C>::zero(&ATyp::scalar());
        let typ = ATyp::scalar();
        
        let result = std::panic::catch_unwind(|| {
            Op::div(a, zero, typ)
        });
        
        assert!(result.is_err());
    }
    
    #[test]
    fn test_op_div_zero_numerator() {
        let zero = GOp::<C>::zero(&ATyp::scalar());
        let b = GOp::<C>::value(&scalar::<C>(5));
        let typ = ATyp::scalar();
        let result = Op::div(zero, b, typ.clone());
        
        assert_eq!(result, Op::zero(&typ));
    }
    
    #[test]
    fn test_op_div_by_one() {
        let a = GOp::<C>::value(&scalar::<C>(42));
        let one = GOp::<C>::one(&ATyp::scalar());
        let typ = ATyp::scalar();
        let result = Op::div(a.clone(), one, typ);
        
        assert_eq!(result, a);
    }
    
    #[test]
    fn test_op_rem_indices() {
        let a = GOp::<C>::Value(Value::Index(10));
        let b = GOp::<C>::Value(Value::Index(3));
        let r = CRange::new(0, 20);
        let typ = ATyp::Base(ABase::Fin(r));
        let result = Op::rem(a, b, typ);
        
        match result {
            Op::Value(_) => (),
            _ => panic!("Expected value from rem of values"),
        }
    }
    
    #[test]
    fn test_op_mul_by_zero() {
        let a = GOp::<C>::value(&scalar::<C>(42));
        let zero = GOp::<C>::zero(&ATyp::scalar());
        let typ = ATyp::scalar();
        let result = Op::mul(a, zero, typ.clone());
        
        assert_eq!(result, Op::zero(&typ));
    }
    
    #[test]
    fn test_op_mul_by_one() {
        let a = GOp::<C>::value(&scalar::<C>(42));
        let one = GOp::<C>::one(&ATyp::scalar());
        let typ = ATyp::scalar();
        let result = Op::mul(a.clone(), one, typ);
        
        assert_eq!(result, a);
    }
    
    #[test]
    fn test_op_add_commutative_fft() {
        let a = GOp::<C>::value(&scalar::<C>(1));
        let b = GOp::<C>::value(&scalar::<C>(2));
        let fft_a = Op::Fft(mk::<C>(a));
        let fft_b = Op::Fft(mk::<C>(b));
        let typ = ATyp::scalar();
        let result = Op::add(fft_a, fft_b, typ);
        
        match result {
            Op::Fft(_) => (),
            _ => panic!("Expected Fft wrapper for add of fft values"),
        }
    }
    
    #[test]
    fn test_op_sub_commutative_ifft() {
        let a = GOp::<C>::value(&scalar::<C>(5));
        let b = GOp::<C>::value(&scalar::<C>(2));
        let ifft_a = Op::Ifft(mk::<C>(a));
        let ifft_b = Op::Ifft(mk::<C>(b));
        let typ = ATyp::scalar();
        let result = Op::sub(ifft_a, ifft_b, typ);
        
        match result {
            Op::Ifft(_) => (),
            _ => panic!("Expected Ifft wrapper for sub of ifft values"),
        }
    }
}
