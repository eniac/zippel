//! Direct unit tests for uncovered Op functions
//! 
//! This module tests specific Op construction and manipulation functions
//! that are not covered by property tests.

#[cfg(test)]
mod op_construction_tests {
    use crate::{Op, GOp};
    use crate::tests::test_helpers::*;
    use backend::{ATyp, Value, ArkConfig};
    use lang::typ::CRange;
    
    type C = TestConfig;
    
    #[test]
    fn test_poly_construction() {
        let val = Op::<C, ()>::value(&scalar::<C>(42));
        let poly_op = Op::poly(val);
        
        match poly_op {
            Op::Poly(inner) => {
                match *inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Poly"),
                }
            }
            _ => panic!("Expected Poly operation"),
        }
    }
    
    #[test]
    fn test_coef_construction() {
        let val = Op::<C, ()>::value(&scalar::<C>(42));
        let coef_op = Op::coef(val);
        
        match coef_op {
            Op::Coef(inner) => {
                match *inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Coef"),
                }
            }
            _ => panic!("Expected Coef operation"),
        }
    }
    
    #[test]
    fn test_mle_construction() {
        let val = Op::<C, ()>::value(&scalar::<C>(42));
        let mle_op = Op::mle(val);
        
        match mle_op {
            Op::Mle(inner) => {
                match *inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Mle"),
                }
            }
            _ => panic!("Expected Mle operation"),
        }
    }
    
    #[test]
    fn test_fft_construction() {
        let val = Op::<C, ()>::value(&scalar::<C>(42));
        let fft_op = Op::fft(val);
        
        match fft_op {
            Op::Fft(inner) => {
                match *inner {
                    Op::Value(_) => (),
                    _ => panic!("Expected Value inside Fft"),
                }
            }
            _ => panic!("Expected Fft operation"),
        }
    }
    
    #[test]
    fn test_ifft_construction() {
        let val = Op::<C, ()>::value(&scalar::<C>(42));
        let ifft_op = Op::ifft(val);
        
        match ifft_op {
            Op::Ifft(inner) => {
                match *inner {
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
        let val = Op::<C, ()>::value(&scalar::<C>(42));
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
        let val = Op::<C, ()>::value(&scalar::<C>(42));
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
        let range_op = Op::<C, ()>::range(range);
        
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
        let zero_op = Op::<C, ()>::zero(&ATyp::scalar());
        match zero_op {
            Op::Value(v) => {
                assert_eq!(v, Value::zero(&ATyp::scalar()));
            }
            _ => panic!("Expected Value"),
        }
    }
    
    #[test]
    fn test_zero_g1() {
        let zero_op = Op::<C, ()>::zero(&ATyp::g1());
        match zero_op {
            Op::Value(v) => {
                assert_eq!(v, Value::zero(&ATyp::g1()));
            }
            _ => panic!("Expected Value"),
        }
    }
    
    #[test]
    fn test_pad_zeroes_no_padding_needed() {
        let vec_val = Op::<C, ()>::vec(vec![
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
    
    #[test]
    fn test_equ_both_values() {
        let v1 = Op::<C, ()>::value(&scalar::<C>(42));
        let v2 = Op::<C, ()>::value(&scalar::<C>(42));
        
        let result = Op::equ(v1, v2);
        
        // When both are values, should evaluate to Bool
        match result {
            Op::Value(Value::Bool(true)) => (),
            _ => panic!("Expected Bool(true) for equal values"),
        }
    }
    
    #[test]
    fn test_equ_different_values() {
        let v1 = Op::<C, ()>::value(&scalar::<C>(42));
        let v2 = Op::<C, ()>::value(&scalar::<C>(17));
        
        let result = Op::equ(v1, v2);
        
        // When both are different values, should evaluate to Bool(false)
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false) for different values"),
        }
    }
    
    #[test]
    fn test_and_both_values() {
        let v1 = Op::<C, ()>::value(&Value::Bool(true));
        let v2 = Op::<C, ()>::value(&Value::Bool(true));
        
        let result = Op::and(v1, v2);
        
        match result {
            Op::Value(Value::Bool(true)) => (),
            _ => panic!("Expected Bool(true)"),
        }
    }
    
    #[test]
    fn test_and_false_shortcircuit_left() {
        let v1 = Op::<C, ()>::value(&Value::Bool(false));
        let v2 = Op::<C, ()>::value(&Value::Bool(true));
        
        let result = Op::and(v1, v2);
        
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false) - short circuit"),
        }
    }
    
    #[test]
    fn test_and_false_shortcircuit_right() {
        let v1 = Op::<C, ()>::value(&Value::Bool(true));
        let v2 = Op::<C, ()>::value(&Value::Bool(false));
        
        let result = Op::and(v1, v2);
        
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false) - short circuit"),
        }
    }
    
    #[test]
    fn test_btrue() {
        let result = Op::<C, ()>::btrue();
        match result {
            Op::Value(Value::Bool(true)) => (),
            _ => panic!("Expected Bool(true)"),
        }
    }
    
    #[test]
    fn test_bfalse() {
        let result = Op::<C, ()>::bfalse();
        match result {
            Op::Value(Value::Bool(false)) => (),
            _ => panic!("Expected Bool(false)"),
        }
    }
    
    #[test]
    fn test_vec_construction() {
        let ops = vec![
            Op::<C, ()>::value(&scalar::<C>(1)),
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
        let challenge = Op::<C, ()>::challenge(ATyp::scalar());
        match challenge {
            Op::Challenge(typ, false) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Challenge"),
        }
    }
    
    #[test]
    fn test_random_construction() {
        let random = Op::<C, ()>::random(ATyp::scalar());
        match random {
            Op::Random(typ, false) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Random"),
        }
    }
    
    #[test]
    fn test_challenge_nz_construction() {
        let challenge = Op::<C, ()>::challenge_nz(ATyp::scalar());
        match challenge {
            Op::Challenge(typ, true) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Challenge with nonzero flag"),
        }
    }
    
    #[test]
    fn test_random_nz_construction() {
        let random = Op::<C, ()>::random_nz(ATyp::scalar());
        match random {
            Op::Random(typ, true) => assert_eq!(typ, ATyp::scalar()),
            _ => panic!("Expected Random with nonzero flag"),
        }
    }
    
    #[test]
    fn test_check_construction() {
        let val = Op::<C, ()>::value(&Value::Bool(true));
        let check = Op::check(val);
        
        match check {
            Op::Check(_) => (),
            _ => panic!("Expected Check"),
        }
    }
    
    #[test]
    fn test_eval_construction() {
        let p = Op::<C, ()>::value(&scalar::<C>(42));
        let x = Op::value(&scalar::<C>(3));
        
        let eval_op = Op::eval(p, x);
        
        match eval_op {
            Op::Eval(_, _) => (),
            _ => panic!("Expected Eval"),
        }
    }
    
    #[test]
    
    #[test]
    fn test_index_construction() {
        let index_op = Op::<C, ()>::index(42);
        match index_op {
            Op::Value(Value::Index(42)) => (),
            _ => panic!("Expected Index value"),
        }
    }
    
    #[test]
    
    #[test]
    
    #[test]
    fn test_pow_construction() {
        let base = Op::<C, ()>::value(&scalar::<C>(2));
        let exp = Op::value(&scalar::<C>(3));
        
        let pow_op = Op::pow(base, exp, ATyp::scalar());
        
        match pow_op {
            Op::Bin(lang::ast::BinOp::Pow, _, _, _) => (),
            _ => panic!("Expected Pow bin op"),
        }
    }
    
    #[test]
    fn test_dot_construction() {
        let v1 = Op::<C, ()>::vec(vec![Op::value(&scalar::<C>(1))]);
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
