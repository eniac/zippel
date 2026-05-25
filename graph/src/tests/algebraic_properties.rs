//! Algebraic Property Tests
//!
//! This module tests that graph operations satisfy mathematical properties
//! through execution. These tests validate semantic correctness of the language.
//!
//! Week 1 Focus:
//! - Scalar field properties (commutativity, associativity, distributivity, identity, inverse)
//! - Basic arithmetic operations
//! - Cross-type properties

#[cfg(test)]
mod scalar_field_properties {
    use crate::Op;
    use crate::tests::test_helpers::*;
    use backend::ATyp;

    type C = TestConfig;

    // ============================================================================
    // SCALAR FIELD ADDITION PROPERTIES
    // ============================================================================

    #[test]
    fn test_scalar_addition_commutativity() {
        // Property: a + b = b + a
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());

        let add_ab = Op::add(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(add_ab);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());

        let add_ba = Op::add(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(a2, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(add_ba);
        let dag2 = builder2.build();

        // Test with multiple inputs
        let test_cases = vec![(3, 5), (0, 7), (10, 0), (1, 1), (42, 17)];

        for (a_val, b_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Commutativity failed for {} + {}",
                a_val,
                b_val
            );
        }
    }

    #[test]
    fn test_scalar_addition_associativity() {
        // Property: (a + b) + c = a + (b + c)
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());

        let ab = Op::add(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder1.add_op(ab);

        let abc_left = Op::add(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(c1, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(abc_left);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());

        let bc = Op::add(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bc_ref = builder2.add_op(bc);

        let abc_right = Op::add(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(bc_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(abc_right);
        let dag2 = builder2.build();

        let test_cases = vec![(1, 2, 3), (5, 0, 7), (0, 0, 0), (10, 20, 30)];

        for (a_val, b_val, c_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);
            add_scalar_input(&mut inputs, "c", c_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Associativity failed for ({} + {}) + {} vs {} + ({} + {})",
                a_val,
                b_val,
                c_val,
                a_val,
                b_val,
                c_val
            );
        }
    }

    #[test]
    fn test_scalar_addition_identity() {
        // Property: a + 0 = a
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let add_zero = Op::add(
            Op::Ref(a, ATyp::scalar()),
            Op::Value(zero_scalar()),
            ATyp::scalar(),
        );
        builder.add_op(add_zero);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = scalar::<C>(a_val);

            assert!(
                values_equal(&result, &expected),
                "Identity failed for {} + 0",
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_addition_zero_commutativity() {
        // Property: 0 + a = a
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let zero_add = Op::add(
            Op::Value(zero_scalar()),
            Op::Ref(a, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(zero_add);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = scalar::<C>(a_val);

            assert!(
                values_equal(&result, &expected),
                "Zero commutativity failed for 0 + {}",
                a_val
            );
        }
    }

    // ============================================================================
    // SCALAR FIELD MULTIPLICATION PROPERTIES
    // ============================================================================

    #[test]
    fn test_scalar_multiplication_commutativity() {
        // Property: a * b = b * a
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());

        let mul_ab = Op::mul(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(mul_ab);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());

        let mul_ba = Op::mul(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(a2, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(mul_ba);
        let dag2 = builder2.build();

        let test_cases = vec![(2, 3), (1, 7), (5, 0), (1, 1), (4, 5)];

        for (a_val, b_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Multiplication commutativity failed for {} * {}",
                a_val,
                b_val
            );
        }
    }

    #[test]
    fn test_scalar_multiplication_associativity() {
        // Property: (a * b) * c = a * (b * c)
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());

        let ab = Op::mul(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder1.add_op(ab);

        let abc_left = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(c1, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(abc_left);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());

        let bc = Op::mul(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bc_ref = builder2.add_op(bc);

        let abc_right = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(bc_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(abc_right);
        let dag2 = builder2.build();

        let test_cases = vec![(2, 3, 4), (1, 5, 7), (2, 2, 2)];

        for (a_val, b_val, c_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);
            add_scalar_input(&mut inputs, "c", c_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Multiplication associativity failed for ({} * {}) * {} vs {} * ({} * {})",
                a_val,
                b_val,
                c_val,
                a_val,
                b_val,
                c_val
            );
        }
    }

    #[test]
    fn test_scalar_multiplication_identity() {
        // Property: a * 1 = a
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let mul_one = Op::mul(
            Op::Ref(a, ATyp::scalar()),
            Op::Value(one_scalar()),
            ATyp::scalar(),
        );
        builder.add_op(mul_one);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = scalar::<C>(a_val);

            assert!(
                values_equal(&result, &expected),
                "Multiplication identity failed for {} * 1",
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_multiplication_one_commutativity() {
        // Property: 1 * a = a
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let one_mul = Op::mul(
            Op::Value(one_scalar()),
            Op::Ref(a, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(one_mul);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = scalar::<C>(a_val);

            assert!(
                values_equal(&result, &expected),
                "One commutativity failed for 1 * {}",
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_multiplication_zero_absorbing() {
        // Property: a * 0 = 0
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let mul_zero = Op::mul(
            Op::Ref(a, ATyp::scalar()),
            Op::Value(zero_scalar()),
            ATyp::scalar(),
        );
        builder.add_op(mul_zero);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = zero_scalar::<C>();

            assert!(
                values_equal(&result, &expected),
                "Zero absorbing property failed for {} * 0",
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_zero_multiplication_commutativity() {
        // Property: 0 * a = 0
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let zero_mul = Op::mul(
            Op::Value(zero_scalar()),
            Op::Ref(a, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(zero_mul);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = zero_scalar::<C>();

            assert!(
                values_equal(&result, &expected),
                "Zero multiplication commutativity failed for 0 * {}",
                a_val
            );
        }
    }

    // ============================================================================
    // SCALAR FIELD DISTRIBUTIVITY
    // ============================================================================

    #[test]
    fn test_scalar_left_distributivity() {
        // Property: a * (b + c) = (a * b) + (a * c)
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());

        let bc = Op::add(
            Op::Ref(b1, ATyp::scalar()),
            Op::Ref(c1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bc_ref = builder1.add_op(bc);

        let left = Op::mul(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(bc_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(left);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());

        let ab = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(b2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder2.add_op(ab);

        let ac = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ac_ref = builder2.add_op(ac);

        let right = Op::add(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(ac_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(right);
        let dag2 = builder2.build();

        let test_cases = vec![(2, 3, 4), (1, 0, 5), (5, 2, 3)];

        for (a_val, b_val, c_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);
            add_scalar_input(&mut inputs, "c", c_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Left distributivity failed for {} * ({} + {}) vs ({} * {}) + ({} * {})",
                a_val,
                b_val,
                c_val,
                a_val,
                b_val,
                a_val,
                c_val
            );
        }
    }

    #[test]
    fn test_scalar_right_distributivity() {
        // Property: (a + b) * c = (a * c) + (b * c)
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());

        let ab = Op::add(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder1.add_op(ab);

        let left = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(c1, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(left);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());

        let ac = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ac_ref = builder2.add_op(ac);

        let bc = Op::mul(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bc_ref = builder2.add_op(bc);

        let right = Op::add(
            Op::Ref(ac_ref, ATyp::scalar()),
            Op::Ref(bc_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(right);
        let dag2 = builder2.build();

        let test_cases = vec![(2, 3, 4), (1, 0, 5), (5, 2, 3)];

        for (a_val, b_val, c_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);
            add_scalar_input(&mut inputs, "c", c_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Right distributivity failed for ({} + {}) * {} vs ({} * {}) + ({} * {})",
                a_val,
                b_val,
                c_val,
                a_val,
                c_val,
                b_val,
                c_val
            );
        }
    }

    // ============================================================================
    // SCALAR FIELD SUBTRACTION PROPERTIES
    // ============================================================================

    #[test]
    fn test_scalar_subtraction_identity() {
        // Property: a - 0 = a
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let sub_zero = Op::sub(
            Op::Ref(a, ATyp::scalar()),
            Op::Value(zero_scalar()),
            ATyp::scalar(),
        );
        builder.add_op(sub_zero);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = scalar::<C>(a_val);

            assert!(
                values_equal(&result, &expected),
                "Subtraction identity failed for {} - 0",
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_subtraction_self_zero() {
        // Property: a - a = 0
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let sub_self = Op::sub(
            Op::Ref(a, ATyp::scalar()),
            Op::Ref(a, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(sub_self);
        let dag = builder.build();

        let test_cases = vec![0, 1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = zero_scalar::<C>();

            assert!(
                values_equal(&result, &expected),
                "Self subtraction failed for {} - {}",
                a_val,
                a_val
            );
        }
    }

    // ============================================================================
    // SCALAR FIELD DIVISION PROPERTIES
    // ============================================================================

    #[test]
    fn test_scalar_division_identity() {
        // Property: a / 1 = a
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let div_one = Op::div(
            Op::Ref(a, ATyp::scalar()),
            Op::Value(one_scalar()),
            ATyp::scalar(),
        );
        builder.add_op(div_one);
        let dag = builder.build();

        let test_cases = vec![1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = scalar::<C>(a_val);

            assert!(
                values_equal(&result, &expected),
                "Division identity failed for {} / 1",
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_division_self_one() {
        // Property: a / a = 1 (for a != 0)
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let div_self = Op::div(
            Op::Ref(a, ATyp::scalar()),
            Op::Ref(a, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(div_self);
        let dag = builder.build();

        let test_cases = vec![1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = one_scalar::<C>();

            assert!(
                values_equal(&result, &expected),
                "Self division failed for {} / {}",
                a_val,
                a_val
            );
        }
    }

    #[test]
    fn test_scalar_zero_division_zero() {
        // Property: 0 / a = 0 (for a != 0)
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());

        let zero_div = Op::div(
            Op::Value(zero_scalar()),
            Op::Ref(a, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(zero_div);
        let dag = builder.build();

        let test_cases = vec![1, 5, 42, 100];

        for a_val in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = zero_scalar::<C>();

            assert!(
                values_equal(&result, &expected),
                "Zero division failed for 0 / {}",
                a_val
            );
        }
    }
}

#[cfg(test)]
mod vector_properties {
    use super::super::test_helpers::*;
    use crate::Op;
    use backend::{ATyp, Value};

    type C = TestConfig;

    #[test]
    fn test_vector_addition_commutativity() {
        // Property: [a, b] + [c, d] = [c, d] + [a, b]
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());
        let d1 = builder1.add_input("d", ATyp::scalar());

        let vec1 = Op::vec(vec![
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
        ]);
        let vec2 = Op::vec(vec![
            Op::Ref(c1, ATyp::scalar()),
            Op::Ref(d1, ATyp::scalar()),
        ]);

        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let add1 = Op::add(vec1, vec2, vec_typ.clone());
        builder1.add_op(add1);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());
        let d2 = builder2.add_input("d", ATyp::scalar());

        let vec1b = Op::vec(vec![
            Op::Ref(c2, ATyp::scalar()),
            Op::Ref(d2, ATyp::scalar()),
        ]);
        let vec2b = Op::vec(vec![
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(b2, ATyp::scalar()),
        ]);

        let add2 = Op::add(vec1b, vec2b, vec_typ);
        builder2.add_op(add2);
        let dag2 = builder2.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 1);
        add_scalar_input(&mut inputs, "b", 2);
        add_scalar_input(&mut inputs, "c", 3);
        add_scalar_input(&mut inputs, "d", 4);

        let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
        let result2 = execute_graph(&dag2, inputs).unwrap();

        assert!(
            values_equal(&result1, &result2),
            "Vector addition commutativity failed"
        );
    }

    #[test]
    fn test_vector_scalar_multiplication_distributivity() {
        // Property: a * [b, c] = [a*b, a*c]
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());

        let vec = Op::vec(vec![
            Op::Ref(b1, ATyp::scalar()),
            Op::Ref(c1, ATyp::scalar()),
        ]);

        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let mul = Op::mul(Op::Ref(a1, ATyp::scalar()), vec, vec_typ.clone());
        builder1.add_op(mul);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());

        let ab = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(b2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ac = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );

        let vec_explicit = Op::vec(vec![ab, ac]);
        builder2.add_op(vec_explicit);
        let dag2 = builder2.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 2);
        add_scalar_input(&mut inputs, "b", 3);
        add_scalar_input(&mut inputs, "c", 5);

        let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
        let result2 = execute_graph(&dag2, inputs).unwrap();

        assert!(
            values_equal(&result1, &result2),
            "Vector scalar multiplication distributivity failed"
        );
    }

    #[test]
    fn test_vector_addition_associativity() {
        // Property: ([a,b] + [c,d]) + [e,f] = [a,b] + ([c,d] + [e,f])
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());
        let d1 = builder1.add_input("d", ATyp::scalar());
        let e1 = builder1.add_input("e", ATyp::scalar());
        let f1 = builder1.add_input("f", ATyp::scalar());

        let vec1 = Op::vec(vec![
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
        ]);
        let vec2 = Op::vec(vec![
            Op::Ref(c1, ATyp::scalar()),
            Op::Ref(d1, ATyp::scalar()),
        ]);
        let vec3 = Op::vec(vec![
            Op::Ref(e1, ATyp::scalar()),
            Op::Ref(f1, ATyp::scalar()),
        ]);

        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let add12 = Op::add(vec1, vec2, vec_typ.clone());
        let add12_ref = builder1.add_op(add12);
        let add123 = Op::add(Op::Ref(add12_ref, vec_typ.clone()), vec3, vec_typ.clone());
        builder1.add_op(add123);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());
        let d2 = builder2.add_input("d", ATyp::scalar());
        let e2 = builder2.add_input("e", ATyp::scalar());
        let f2 = builder2.add_input("f", ATyp::scalar());

        let vec1b = Op::vec(vec![
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(b2, ATyp::scalar()),
        ]);
        let vec2b = Op::vec(vec![
            Op::Ref(c2, ATyp::scalar()),
            Op::Ref(d2, ATyp::scalar()),
        ]);
        let vec3b = Op::vec(vec![
            Op::Ref(e2, ATyp::scalar()),
            Op::Ref(f2, ATyp::scalar()),
        ]);

        let add23 = Op::add(vec2b, vec3b, vec_typ.clone());
        let add23_ref = builder2.add_op(add23);
        let add123b = Op::add(vec1b, Op::Ref(add23_ref, vec_typ.clone()), vec_typ.clone());
        builder2.add_op(add123b);
        let dag2 = builder2.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 1);
        add_scalar_input(&mut inputs, "b", 2);
        add_scalar_input(&mut inputs, "c", 3);
        add_scalar_input(&mut inputs, "d", 4);
        add_scalar_input(&mut inputs, "e", 5);
        add_scalar_input(&mut inputs, "f", 6);

        let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
        let result2 = execute_graph(&dag2, inputs).unwrap();

        assert!(
            values_equal(&result1, &result2),
            "Vector addition associativity failed"
        );
    }

    #[test]
    fn test_vector_addition_identity() {
        // Property: [a,b] + [0,0] = [a,b]
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());
        let b = builder.add_input("b", ATyp::scalar());

        let vec = Op::vec(vec![Op::Ref(a, ATyp::scalar()), Op::Ref(b, ATyp::scalar())]);
        let zero_vec = Op::vec(vec![Op::Value(zero_scalar()), Op::Value(zero_scalar())]);

        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let add = Op::add(vec, zero_vec, vec_typ);
        builder.add_op(add);
        let dag = builder.build();

        let test_cases = vec![(1, 2), (0, 0), (5, 10), (42, 17)];

        for (a_val, b_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);

            let result = execute_graph(&dag, inputs).unwrap();
            let expected = Value::value_vec(vec![scalar::<C>(a_val), scalar::<C>(b_val)]);

            assert!(
                values_equal(&result, &expected),
                "Vector addition identity failed for [{}, {}]",
                a_val,
                b_val
            );
        }
    }
}

#[cfg(test)]
mod complex_properties {
    use super::super::test_helpers::*;
    use crate::Op;
    use backend::ATyp;

    type C = TestConfig;

    #[test]
    fn test_nested_distributivity() {
        // Property: a * (b + (c + d)) = a*b + a*c + a*d
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());
        let d1 = builder1.add_input("d", ATyp::scalar());

        let cd = Op::add(
            Op::Ref(c1, ATyp::scalar()),
            Op::Ref(d1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let cd_ref = builder1.add_op(cd);

        let bcd = Op::add(
            Op::Ref(b1, ATyp::scalar()),
            Op::Ref(cd_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bcd_ref = builder1.add_op(bcd);

        let left = Op::mul(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(bcd_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(left);
        let dag1 = builder1.build();

        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());
        let d2 = builder2.add_input("d", ATyp::scalar());

        let ab = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(b2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder2.add_op(ab);

        let ac = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ac_ref = builder2.add_op(ac);

        let ad = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(d2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ad_ref = builder2.add_op(ad);

        let ab_ac = Op::add(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(ac_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ac_ref = builder2.add_op(ab_ac);

        let right = Op::add(
            Op::Ref(ab_ac_ref, ATyp::scalar()),
            Op::Ref(ad_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(right);
        let dag2 = builder2.build();

        let test_cases = vec![(2, 3, 4, 5), (1, 0, 0, 0), (5, 1, 2, 3)];

        for (a_val, b_val, c_val, d_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);
            add_scalar_input(&mut inputs, "c", c_val);
            add_scalar_input(&mut inputs, "d", d_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Nested distributivity failed for {} * ({} + {} + {})",
                a_val,
                b_val,
                c_val,
                d_val
            );
        }
    }

    #[test]
    fn test_mixed_operations_consistency() {
        // Property: (a + b) * (c - d) computed two ways should be equal
        let mut builder1 = GraphBuilder::<C>::new();
        let a1 = builder1.add_input("a", ATyp::scalar());
        let b1 = builder1.add_input("b", ATyp::scalar());
        let c1 = builder1.add_input("c", ATyp::scalar());
        let d1 = builder1.add_input("d", ATyp::scalar());

        let ab = Op::add(
            Op::Ref(a1, ATyp::scalar()),
            Op::Ref(b1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder1.add_op(ab);

        let cd = Op::sub(
            Op::Ref(c1, ATyp::scalar()),
            Op::Ref(d1, ATyp::scalar()),
            ATyp::scalar(),
        );
        let cd_ref = builder1.add_op(cd);

        let result_op = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(cd_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder1.add_op(result_op);
        let dag1 = builder1.build();

        // Expand: (a+b)*(c-d) = a*c - a*d + b*c - b*d
        let mut builder2 = GraphBuilder::<C>::new();
        let a2 = builder2.add_input("a", ATyp::scalar());
        let b2 = builder2.add_input("b", ATyp::scalar());
        let c2 = builder2.add_input("c", ATyp::scalar());
        let d2 = builder2.add_input("d", ATyp::scalar());

        let ac = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ac_ref = builder2.add_op(ac);

        let ad = Op::mul(
            Op::Ref(a2, ATyp::scalar()),
            Op::Ref(d2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ad_ref = builder2.add_op(ad);

        let bc = Op::mul(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(c2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bc_ref = builder2.add_op(bc);

        let bd = Op::mul(
            Op::Ref(b2, ATyp::scalar()),
            Op::Ref(d2, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bd_ref = builder2.add_op(bd);

        let ac_minus_ad = Op::sub(
            Op::Ref(ac_ref, ATyp::scalar()),
            Op::Ref(ad_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ac_minus_ad_ref = builder2.add_op(ac_minus_ad);

        let bc_minus_bd = Op::sub(
            Op::Ref(bc_ref, ATyp::scalar()),
            Op::Ref(bd_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        let bc_minus_bd_ref = builder2.add_op(bc_minus_bd);

        let final_result = Op::add(
            Op::Ref(ac_minus_ad_ref, ATyp::scalar()),
            Op::Ref(bc_minus_bd_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder2.add_op(final_result);
        let dag2 = builder2.build();

        let test_cases = vec![(2, 3, 5, 1), (1, 1, 1, 1), (10, 5, 8, 3)];

        for (a_val, b_val, c_val, d_val) in test_cases {
            let mut inputs = test_inputs();
            add_scalar_input(&mut inputs, "a", a_val);
            add_scalar_input(&mut inputs, "b", b_val);
            add_scalar_input(&mut inputs, "c", c_val);
            add_scalar_input(&mut inputs, "d", d_val);

            let result1 = execute_graph(&dag1, inputs.clone()).unwrap();
            let result2 = execute_graph(&dag2, inputs).unwrap();

            assert!(
                values_equal(&result1, &result2),
                "Mixed operations consistency failed for ({} + {}) * ({} - {})",
                a_val,
                b_val,
                c_val,
                d_val
            );
        }
    }
}
