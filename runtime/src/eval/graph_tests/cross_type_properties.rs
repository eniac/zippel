//! Cross-type algebraic property tests
//!
//! Tests that verify algebraic properties hold across different types:
//! - Scalar * G1 point operations
//! - Scalar * G2 point operations  

#[cfg(test)]
mod scalar_g1_properties {
    use crate::eval::graph_tests::helpers::*;
    use backend::{ATyp, Value};
    use graph::Op;
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
    use crate::eval::graph_tests::helpers::*;
    use backend::poly::variant::DenseMle;
    use backend::{ATyp, PolyVariant, Value, VirtualPolynomial};
    use lang::id::Vid;
    use share::Ctx;

    type C = TestConfig;
    type Fr = <C as backend::Backend>::F;

    #[test]
    fn test_mle_app_evaluation_differential() {
        let src = r#"
            fn f<F: Field>(instance p: Mle<F, 2>, instance x: F) -> [F; 2] {
                coef(p(x))
            }
        "#;
        let dags = lowered::<C>(src, &Ctx::new()).unwrap();
        let dag = &dags[0];

        let mut rng = ark_std::test_rng();
        // Generate random 4 evaluations
        let v0 = Fr::from(10);
        let v1 = Fr::from(20);
        let v2 = Fr::from(30);
        let v3 = Fr::from(40);

        let mle_poly = PolyVariant::DenseMle(DenseMle::new(2, vec![v0, v1, v2, v3]));
        let p_val = Value::poly(VirtualPolynomial::from_poly(mle_poly));

        let x_val = Value::<C>::random(&mut rng, &ATyp::scalar());
        let x_scalar = match &x_val {
            Value::Scalar(s) => *s,
            _ => unreachable!(),
        };

        // `p(x)` is `eval(p, [x])`: it fixes variable 0, the low bit of an evaluation's
        // index, leaving the MLE [v0 + (v1 - v0)*x, v2 + (v3 - v2)*x].
        let e0 = v0 + (v1 - v0) * x_scalar;
        let e1 = v2 + (v3 - v2) * x_scalar;

        let expected_result = Value::vec_scalar(vec![e0, e1]);

        let mut inputs = test_inputs();
        inputs.insert(&Vid::from("p"), &p_val);
        inputs.insert(&Vid::from("x"), &x_val);

        let actual_result = execute_graph(dag, inputs).unwrap();

        assert!(
            values_equal(&actual_result, &expected_result),
            "Compiled MLE evaluation should match expected mathematical fold result. Got: {:?}, Expected: {:?}",
            actual_result,
            expected_result
        );
    }

    /// The MLE with evaluations `[10, 20, 30, 40]`, as a value.
    fn mle_10_to_40() -> Value<C> {
        let evals = [10, 20, 30, 40].map(Fr::from).to_vec();
        let mle = PolyVariant::DenseMle(DenseMle::new(2, evals));
        Value::poly(VirtualPolynomial::from_poly(mle))
    }

    /// `f(p, x, y)` for the MLE `[10, 20, 30, 40]` at random `x`, `y`, with the expected value.
    fn run_at_point(body: &str) -> (Value<C>, Fr) {
        let src = format!(
            "fn f<F: Field>(instance p: Mle<F, 2>, instance x: F, instance y: F) -> F {{ {body} }}"
        );
        let dags = lowered::<C>(&src, &Ctx::new()).unwrap();
        let mut rng = ark_std::test_rng();
        let scalar = |rng: &mut _| match Value::<C>::random(rng, &ATyp::scalar()) {
            Value::Scalar(s) => s,
            _ => unreachable!(),
        };
        let (x, y) = (scalar(&mut rng), scalar(&mut rng));
        let mut inputs = test_inputs();
        inputs.insert(&Vid::from("p"), &mle_10_to_40());
        inputs.insert(&Vid::from("x"), &Value::Scalar(x));
        inputs.insert(&Vid::from("y"), &Value::Scalar(y));
        // `x` fixes variable 0 (the low bit of an index), `y` variable 1: 10 + 10x + 20y.
        let expected = Fr::from(10) + Fr::from(10) * x + Fr::from(20) * y;
        (execute_graph(&dags[0], inputs).unwrap(), expected)
    }

    /// Applying an MLE is `eval`, at a whole point or one coordinate at a time: each coordinate
    /// fixes the next variable from the low bit. `p([x, y])` used to fold the point elementwise
    /// into a vector, and `q(y)` on the one-variable `q = p(x)` read `q` as a line.
    #[test]
    fn test_mle_app_is_eval() {
        for body in [
            "eval(p, [x, y])",
            "p([x, y])",
            "let pt = [x, y]; p(pt)",
            "let q = p(x); q(y)",
        ] {
            let (actual, expected) = run_at_point(body);
            assert!(
                values_equal(&actual, &Value::Scalar(expected)),
                "{body}: got {actual:?}, expected {expected:?}"
            );
        }
    }
}

#[cfg(test)]
mod multivariate_app_tests {
    use crate::eval::graph_tests::helpers::*;
    use backend::poly::variant::{Multivariate, Term};
    use backend::{ATyp, PolyVariant, Value, VirtualPolynomial};
    use lang::id::Vid;
    use share::Ctx;

    type C = TestConfig;
    type Fr = <C as backend::Backend>::F;

    /// Applying a general polynomial (two variables, degree 2) is `eval`, at a whole point or
    /// one coordinate at a time; fixing a leading variable used to panic at run time ("MLE
    /// evaluation failed"), and applying it was not accepted at all.
    #[test]
    fn test_poly_app_is_eval() {
        // p(x0, x1) = 3 + 2·x0 + 5·x0·x1 + 7·x1^2
        let term = |vars: Vec<(usize, usize)>| Term::new(vars);
        let p = Multivariate::new(
            2,
            vec![
                (Fr::from(3), term(vec![])),
                (Fr::from(2), term(vec![(0, 1)])),
                (Fr::from(5), term(vec![(0, 1), (1, 1)])),
                (Fr::from(7), term(vec![(1, 2)])),
            ],
        );
        let p_val = || {
            Value::<C>::poly(VirtualPolynomial::from_poly(
                PolyVariant::SparseMultivariate(p.clone()),
            ))
        };
        let mut rng = ark_std::test_rng();
        let mut scalar = || match Value::<C>::random(&mut rng, &ATyp::scalar()) {
            Value::Scalar(s) => s,
            _ => unreachable!(),
        };
        let (x, y) = (scalar(), scalar());
        let expected = Fr::from(3) + Fr::from(2) * x + Fr::from(5) * x * y + Fr::from(7) * y * y;
        for body in [
            "eval(p, [x, y])",
            "p([x, y])",
            "let q = p(x); q(y)",
            "let q = eval(p, [x]); q(y)",
        ] {
            let src = format!(
                "fn f<F: Field>(instance p: Poly<F, 2, 2>, instance x: F, instance y: F) -> F {{ {body} }}"
            );
            let dags = lowered::<C>(&src, &Ctx::new()).unwrap();
            let mut inputs = test_inputs();
            inputs.insert(&Vid::from("p"), &p_val());
            inputs.insert(&Vid::from("x"), &Value::Scalar(x));
            inputs.insert(&Vid::from("y"), &Value::Scalar(y));
            let actual = execute_graph(&dags[0], inputs).unwrap();
            assert!(
                values_equal(&actual, &Value::Scalar(expected)),
                "{body}: got {actual:?}, expected {expected:?}"
            );
        }
    }
}
