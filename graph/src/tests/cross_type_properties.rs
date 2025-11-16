//! Cross-type algebraic property tests
//! 
//! Tests that verify algebraic properties hold across different types:
//! - Scalar * G1 point operations
//! - Scalar * G2 point operations  

#[cfg(test)]
mod scalar_g1_properties {
    use crate::tests::test_helpers::*;
    use crate::{Op};
    use backend::{ATyp, Value};
    use lang::id::Vid;
    

    type C = TestConfig;

    /// Test: (a + b) * P = a*P + b*P (scalar distributivity over G1 addition)
    #[test]
    fn test_scalar_mul_g1_distributive_scalars() {
        // Build graph for (a + b) * P
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let p1 = builder1.add_input("p", ATyp::g1());
        
        let sum = Op::add(
            Op::Ref(a1.clone(), ATyp::scalar()),
            Op::Ref(b1.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let sum_ref = builder1.add_op(sum);
        
        let lhs = Op::mul(
            Op::Ref(sum_ref, ATyp::scalar()),
            Op::Ref(p1.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        builder1.add_op(lhs);
        let dag1 = builder1.build();

        // Build graph for a*P + b*P
        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let p2 = builder2.add_input("p", ATyp::g1());
        
        let ap = Op::mul(
            Op::Ref(a2.clone(), ATyp::scalar()),
            Op::Ref(p2.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        let ap_ref = builder2.add_op(ap);
        
        let bp = Op::mul(
            Op::Ref(b2.clone(), ATyp::scalar()),
            Op::Ref(p2.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        let bp_ref = builder2.add_op(bp);
        
        let rhs = Op::add(
            Op::Ref(ap_ref, ATyp::g1()),
            Op::Ref(bp_ref, ATyp::g1()),
            ATyp::g1(),
        );
        builder2.add_op(rhs);
        let dag2 = builder2.build();

        // Test with random inputs
        let mut rng = ark_std::test_rng();
        for _ in 0..3 {
            let a_val = Value::<C>::random(&mut rng, &ATyp::scalar());
            let b_val = Value::<C>::random(&mut rng, &ATyp::scalar());
            let p_val = Value::<C>::random(&mut rng, &ATyp::g1());
            
            let mut inputs = test_inputs();
            inputs.insert(&Vid::from("a"), &a_val);
            inputs.insert(&Vid::from("b"), &b_val);
            inputs.insert(&Vid::from("p"), &p_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "(a+b)*P should equal a*P + b*P"
            );
        }
    }

    /// Test: a * (P + Q) = a*P + a*Q (scalar distributivity over G1 point addition)
    #[test]
    fn test_scalar_mul_g1_distributive_points() {
        // Build graph for a * (P + Q)
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let p1 = builder1.add_input("p", ATyp::g1());
        let q1 = builder1.add_input("q", ATyp::g1());
        
        let sum = Op::add(
            Op::Ref(p1.clone(), ATyp::g1()),
            Op::Ref(q1.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        let sum_ref = builder1.add_op(sum);
        
        let lhs = Op::mul(
            Op::Ref(a1.clone(), ATyp::scalar()),
            Op::Ref(sum_ref, ATyp::g1()),
            ATyp::g1(),
        );
        builder1.add_op(lhs);
        let dag1 = builder1.build();

        // Build graph for a*P + a*Q
        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let p2 = builder2.add_input("p", ATyp::g1());
        let q2 = builder2.add_input("q", ATyp::g1());
        
        let ap = Op::mul(
            Op::Ref(a2.clone(), ATyp::scalar()),
            Op::Ref(p2.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        let ap_ref = builder2.add_op(ap);
        
        let aq = Op::mul(
            Op::Ref(a2.clone(), ATyp::scalar()),
            Op::Ref(q2.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        let aq_ref = builder2.add_op(aq);
        
        let rhs = Op::add(
            Op::Ref(ap_ref, ATyp::g1()),
            Op::Ref(aq_ref, ATyp::g1()),
            ATyp::g1(),
        );
        builder2.add_op(rhs);
        let dag2 = builder2.build();

        // Test with random inputs
        let mut rng = ark_std::test_rng();
        for _ in 0..3 {
            let a_val = Value::<C>::random(&mut rng, &ATyp::scalar());
            let p_val = Value::<C>::random(&mut rng, &ATyp::g1());
            let q_val = Value::<C>::random(&mut rng, &ATyp::g1());
            
            let mut inputs = test_inputs();
            inputs.insert(&Vid::from("a"), &a_val);
            inputs.insert(&Vid::from("p"), &p_val);
            inputs.insert(&Vid::from("q"), &q_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "a*(P+Q) should equal a*P + a*Q"
            );
        }
    }

    /// Test: (a * b) * P = a * (b * P) (scalar multiplication associativity with G1)
    #[test]
    fn test_scalar_mul_g1_associativity() {
        // Build graph for (a * b) * P
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let p1 = builder1.add_input("p", ATyp::g1());
        
        let ab = Op::mul(
            Op::Ref(a1.clone(), ATyp::scalar()),
            Op::Ref(b1.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder1.add_op(ab);
        
        let lhs = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(p1.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        builder1.add_op(lhs);
        let dag1 = builder1.build();

        // Build graph for a * (b * P)
        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let p2 = builder2.add_input("p", ATyp::g1());
        
        let bp = Op::mul(
            Op::Ref(b2.clone(), ATyp::scalar()),
            Op::Ref(p2.clone(), ATyp::g1()),
            ATyp::g1(),
        );
        let bp_ref = builder2.add_op(bp);
        
        let rhs = Op::mul(
            Op::Ref(a2.clone(), ATyp::scalar()),
            Op::Ref(bp_ref, ATyp::g1()),
            ATyp::g1(),
        );
        builder2.add_op(rhs);
        let dag2 = builder2.build();

        // Test with random inputs
        let mut rng = ark_std::test_rng();
        for _ in 0..3 {
            let a_val = Value::<C>::random(&mut rng, &ATyp::scalar());
            let b_val = Value::<C>::random(&mut rng, &ATyp::scalar());
            let p_val = Value::<C>::random(&mut rng, &ATyp::g1());
            
            let mut inputs = test_inputs();
            inputs.insert(&Vid::from("a"), &a_val);
            inputs.insert(&Vid::from("b"), &b_val);
            inputs.insert(&Vid::from("p"), &p_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "(a*b)*P should equal a*(b*P)"
            );
        }
    }
}
