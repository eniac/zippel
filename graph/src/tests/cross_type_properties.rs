//! Cross-type algebraic property tests
//!
//! Tests that verify algebraic properties hold across different types:
//! - Scalar * G1 point operations
//! - Scalar * G2 point operations  

#[cfg(test)]
mod scalar_g1_properties {
    use crate::Op;
    use crate::tests::test_helpers::*;
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
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let sum_ref = builder1.add_op(sum);

        let lhs = Op::mul(
            Op::Ref(sum_ref, ATyp::scalar()),
            Op::Ref(p1, ATyp::g1()),
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
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(p2, ATyp::g1()),
            ATyp::g1(),
        );
        let ap_ref = builder2.add_op(ap);

        let bp = Op::mul(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(p2, ATyp::g1()),
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

        let sum = Op::add(Op::Ref(p1, ATyp::g1()), Op::Ref(q1, ATyp::g1()), ATyp::g1());
        let sum_ref = builder1.add_op(sum);

        let lhs = Op::mul(
            Op::Ref(a1, ATyp::scalar()),
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
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(p2, ATyp::g1()),
            ATyp::g1(),
        );
        let ap_ref = builder2.add_op(ap);

        let aq = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(q2, ATyp::g1()),
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
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder1.add_op(ab);

        let lhs = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(p1, ATyp::g1()),
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
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(p2, ATyp::g1()),
            ATyp::g1(),
        );
        let bp_ref = builder2.add_op(bp);

        let rhs = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
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

#[cfg(test)]
mod mle_differential_tests {
    use crate::tests::test_helpers::*;
    use ark_poly::DenseMultilinearExtension;
    use backend::{ATyp, Value, poly_variant::PolyVariant, virtual_polynomial::VirtualPolynomial};
    use lang::ast::UModule;
    use lang::id::Vid;
    use share::Ctx;

    type C = TestConfig;
    type Fr = <C as backend::ArkConfig>::F;

    #[test]
    fn test_mle_app_evaluation_differential() {
        let src = r#"
            fn f<F: Field>(public p: Mle<F, 2>, public x: F) -> Mle<F, 1> {
                p(x)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let dags = crate::UDags::<C>::from_module(m).unwrap();
        let dag = &dags[0];

        let mut rng = ark_std::test_rng();
        // Generate random 4 evaluations
        let v0 = Fr::from(10);
        let v1 = Fr::from(20);
        let v2 = Fr::from(30);
        let v3 = Fr::from(40);

        let mle_poly = PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
            2,
            vec![v0, v1, v2, v3],
        ));
        let p_val = Value::Poly(VirtualPolynomial::from_poly(mle_poly));

        let x_val = Value::<C>::random(&mut rng, &ATyp::scalar());
        let x_scalar = match &x_val {
            Value::Scalar(s) => *s,
            _ => unreachable!(),
        };

        // Expected output is a 2-element vector:
        // [v0 + (v2 - v0)*x, v1 + (v3 - v1)*x]
        let e0 = v0 + (v2 - v0) * x_scalar;
        let e1 = v1 + (v3 - v1) * x_scalar;

        let expected_result = Value::VecScalar(vec![e0, e1]);

        let mut inputs = test_inputs();
        inputs.insert(&Vid::from("p"), &p_val);
        inputs.insert(&Vid::from("x"), &x_val);

        let actual_result = execute_graph(&dag, inputs).unwrap();

        assert!(
            values_equal(&actual_result, &expected_result),
            "Compiled MLE evaluation should match expected mathematical fold result. Got: {:?}, Expected: {:?}",
            actual_result,
            expected_result
        );
    }
}
