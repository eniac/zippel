/// Basic Operation Tests
///
/// This module tests individual graph operation constructors
/// and basic functionality.

#[cfg(test)]
mod op_construction {
    use crate::tests::test_helpers::*;
    use crate::{Op, GOp};
    use backend::{ATyp, Value};
    use lang::ast::BinOp;

    type C = TestConfig;

    // ============================================================================
    // VALUE OPERATIONS
    // ============================================================================

    #[test]
    fn test_op_value_scalar() {
        let val = scalar::<C>(42);
        let op: GOp<C> = Op::Value(val.clone());
        
        match op {
            Op::Value(v) => assert!(values_equal(&v, &val)),
            _ => panic!("Expected Value operation"),
        }
    }

    #[test]
    fn test_op_value_zero() {
        let zero = zero_scalar::<C>();
        let op: GOp<C> = Op::Value(zero.clone());
        
        match &op {
            Op::Value(v) => assert!(values_equal(v, &zero)),
            _ => panic!("Expected Value operation"),
        }
    }

    #[test]
    fn test_op_value_one() {
        let one = one_scalar::<C>();
        let op: GOp<C> = Op::Value(one.clone());
        
        match &op {
            Op::Value(v) => assert!(values_equal(v, &one)),
            _ => panic!("Expected Value operation"),
        }
    }

    // ============================================================================
    // ADDITION OPERATION SIMPLIFICATIONS
    // ============================================================================

    #[test]
    fn test_op_add_simplification_zero_left() {
        // 0 + v should simplify to v
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let op: GOp<C> = Op::add(
            Op::Value(zero),
            Op::Value(v.clone()),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &v)),
            _ => panic!("Expected simplification to Value"),
        }
    }

    #[test]
    fn test_op_add_simplification_zero_right() {
        // v + 0 should simplify to v
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let op: GOp<C> = Op::add(
            Op::Value(v.clone()),
            Op::Value(zero),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &v)),
            _ => panic!("Expected simplification to Value"),
        }
    }

    #[test]
    fn test_op_add_values() {
        // v1 + v2 should compute the result
        let v1 = scalar::<C>(3);
        let v2 = scalar::<C>(4);
        let expected = scalar::<C>(7);
        
        let op: GOp<C> = Op::add(
            Op::Value(v1),
            Op::Value(v2),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &expected)),
            _ => panic!("Expected Value after addition"),
        }
    }

    // ============================================================================
    // SUBTRACTION OPERATION SIMPLIFICATIONS
    // ============================================================================

    #[test]
    fn test_op_sub_simplification_zero() {
        // v - 0 should simplify to v
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let op: GOp<C> = Op::sub(
            Op::Value(v.clone()),
            Op::Value(zero),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &v)),
            _ => panic!("Expected simplification to Value"),
        }
    }

    #[test]
    fn test_op_sub_values() {
        // v1 - v2 should compute the result
        let v1 = scalar::<C>(10);
        let v2 = scalar::<C>(3);
        let expected = scalar::<C>(7);
        
        let op: GOp<C> = Op::sub(
            Op::Value(v1),
            Op::Value(v2),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &expected)),
            _ => panic!("Expected Value after subtraction"),
        }
    }

    // ============================================================================
    // MULTIPLICATION OPERATION SIMPLIFICATIONS
    // ============================================================================

    #[test]
    fn test_op_mul_simplification_zero_left() {
        // 0 * v should simplify to 0
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let op: GOp<C> = Op::mul(
            Op::Value(zero.clone()),
            Op::Value(v),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &zero)),
            _ => panic!("Expected simplification to zero"),
        }
    }

    #[test]
    fn test_op_mul_simplification_zero_right() {
        // v * 0 should simplify to 0
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let op: GOp<C> = Op::mul(
            Op::Value(v),
            Op::Value(zero.clone()),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &zero)),
            _ => panic!("Expected simplification to zero"),
        }
    }

    #[test]
    fn test_op_mul_simplification_one_left() {
        // 1 * v should simplify to v
        let v = scalar::<C>(42);
        let one = one_scalar::<C>();
        
        let op: GOp<C> = Op::mul(
            Op::Value(one),
            Op::Value(v.clone()),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &v)),
            _ => panic!("Expected simplification to Value"),
        }
    }

    #[test]
    fn test_op_mul_simplification_one_right() {
        // v * 1 should simplify to v
        let v = scalar::<C>(42);
        let one = one_scalar::<C>();
        
        let op: GOp<C> = Op::mul(
            Op::Value(v.clone()),
            Op::Value(one),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &v)),
            _ => panic!("Expected simplification to Value"),
        }
    }

    #[test]
    fn test_op_mul_values() {
        // v1 * v2 should compute the result
        let v1 = scalar::<C>(3);
        let v2 = scalar::<C>(4);
        let expected = scalar::<C>(12);
        
        let op: GOp<C> = Op::mul(
            Op::Value(v1),
            Op::Value(v2),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &expected)),
            _ => panic!("Expected Value after multiplication"),
        }
    }

    // ============================================================================
    // DIVISION OPERATION SIMPLIFICATIONS
    // ============================================================================

    #[test]
    fn test_op_div_simplification_zero_numerator() {
        // 0 / v should simplify to 0
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let op: GOp<C> = Op::div(
            Op::Value(zero.clone()),
            Op::Value(v),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &zero)),
            _ => panic!("Expected simplification to zero"),
        }
    }

    #[test]
    fn test_op_div_simplification_one_denominator() {
        // v / 1 should simplify to v
        let v = scalar::<C>(42);
        let one = one_scalar::<C>();
        
        let op: GOp<C> = Op::div(
            Op::Value(v.clone()),
            Op::Value(one),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &v)),
            _ => panic!("Expected simplification to Value"),
        }
    }

    #[test]
    fn test_op_div_values() {
        // v1 / v2 should compute the result
        let v1 = scalar::<C>(12);
        let v2 = scalar::<C>(3);
        let expected = scalar::<C>(4);
        
        let op: GOp<C> = Op::div(
            Op::Value(v1),
            Op::Value(v2),
            ATyp::scalar(),
        );
        
        match op {
            Op::Value(result) => assert!(values_equal(&result, &expected)),
            _ => panic!("Expected Value after division"),
        }
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_op_div_by_zero() {
        let v = scalar::<C>(42);
        let zero = zero_scalar::<C>();
        
        let _op: GOp<C> = Op::div(
            Op::Value(v),
            Op::Value(zero),
            ATyp::scalar(),
        );
    }

    // ============================================================================
    // VECTOR OPERATIONS
    // ============================================================================

    #[test]
    fn test_op_vec_construction() {
        let v1 = scalar::<C>(1);
        let v2 = scalar::<C>(2);
        let v3 = scalar::<C>(3);
        
        let op: GOp<C> = Op::vec(vec![
            Op::Value(v1),
            Op::Value(v2),
            Op::Value(v3),
        ]);
        
        match op {
            Op::Vec(elements) => assert_eq!(elements.len(), 3),
            _ => panic!("Expected Vec operation"),
        }
    }

    #[test]
    fn test_op_vec_add() {
        let vec1 = Op::vec(vec![
            Op::Value(scalar::<C>(1)),
            Op::Value(scalar::<C>(2)),
        ]);
        
        let vec2 = Op::vec(vec![
            Op::Value(scalar::<C>(3)),
            Op::Value(scalar::<C>(4)),
        ]);
        
        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let op: GOp<C> = Op::add(vec1, vec2, vec_typ);
        
        match op {
            Op::Vec(elements) => {
                assert_eq!(elements.len(), 2);
                // Each element should be an addition
                for elem in &elements {
                    match &**elem {
                        Op::Bin(BinOp::Add, _, _, _) | Op::Value(_) => {}
                        _ => panic!("Expected addition or value in vector elements"),
                    }
                }
            }
            _ => panic!("Expected Vec after vector addition"),
        }
    }

    #[test]
    fn test_op_vec_scalar_mul() {
        let scalar_val = Op::Value(scalar::<C>(2));
        let vec = Op::vec(vec![
            Op::Value(scalar::<C>(3)),
            Op::Value(scalar::<C>(4)),
        ]);
        
        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let op: GOp<C> = Op::mul(scalar_val, vec, vec_typ);
        
        match op {
            Op::Vec(elements) => {
                assert_eq!(elements.len(), 2);
            }
            _ => panic!("Expected Vec after scalar multiplication"),
        }
    }

    // ============================================================================
    // CONCATENATION OPERATIONS
    // ============================================================================

    #[test]
    fn test_op_concat_vectors() {
        let vec1 = Op::vec(vec![
            Op::Value(scalar::<C>(1)),
            Op::Value(scalar::<C>(2)),
        ]);
        
        let vec2 = Op::vec(vec![
            Op::Value(scalar::<C>(3)),
            Op::Value(scalar::<C>(4)),
        ]);
        
        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 4);
        let op: GOp<C> = Op::concat(vec1, vec2, vec_typ);
        
        match op {
            Op::Vec(elements) => {
                assert_eq!(elements.len(), 4);
            }
            _ => panic!("Expected Vec after concatenation"),
        }
    }

    // ============================================================================
    // RAM (RANDOM ACCESS) OPERATIONS
    // ============================================================================

    #[test]
    fn test_op_ram_construction() {
        let vec = Op::vec(vec![
            Op::Value(scalar::<C>(10)),
            Op::Value(scalar::<C>(20)),
            Op::Value(scalar::<C>(30)),
            Op::Value(scalar::<C>(40)),
        ]);
        let idx = Op::Value(Value::Index(2));
        
        let op: GOp<C> = Op::ram(vec, idx);
        
        // RAM operation should be created (may be simplified)
        // Just verify it doesn't panic
        match op {
            Op::Ram(_, _) | Op::Value(_) => {
                // Either simplified to value or kept as RAM
            }
            _ => panic!("Unexpected operation type"),
        }
    }
}

#[cfg(test)]
mod op_integration {
    use crate::tests::test_helpers::*;
    use crate::Op;
    use backend::{ATyp, Value};

    type C = TestConfig;

    #[test]
    fn test_chained_operations() {
        // Test: (a + b) * c - d
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());
        let b = builder.add_input("b", ATyp::scalar());
        let c = builder.add_input("c", ATyp::scalar());
        let d = builder.add_input("d", ATyp::scalar());
        
        let ab = Op::add(
            Op::Ref(a.clone(), ATyp::scalar()),
            Op::Ref(b.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder.add_op(ab);
        
        let abc = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(c.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let abc_ref = builder.add_op(abc);
        
        let result = Op::sub(
            Op::Ref(abc_ref, ATyp::scalar()),
            Op::Ref(d.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(result);
        let dag = builder.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 2);
        add_scalar_input(&mut inputs, "b", 3);
        add_scalar_input(&mut inputs, "c", 4);
        add_scalar_input(&mut inputs, "d", 5);

        let result = execute_graph(&dag, inputs).unwrap();
        // (2 + 3) * 4 - 5 = 5 * 4 - 5 = 20 - 5 = 15
        let expected = scalar::<C>(15);

        assert!(
            values_equal(&result, &expected),
            "Chained operations should compute correctly"
        );
    }

    #[test]
    fn test_multiple_outputs() {
        // Create a graph that computes both a+b and a*b
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());
        let b = builder.add_input("b", ATyp::scalar());
        
        let add_result = Op::add(
            Op::Ref(a.clone(), ATyp::scalar()),
            Op::Ref(b.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let add_ref = builder.add_op(add_result);
        
        let mul_result = Op::mul(
            Op::Ref(a.clone(), ATyp::scalar()),
            Op::Ref(b.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let mul_ref = builder.add_op(mul_result);
        
        // Create a vector with both results
        let vec_result = Op::vec(vec![
            Op::Ref(add_ref, ATyp::scalar()),
            Op::Ref(mul_ref, ATyp::scalar()),
        ]);
        builder.add_op(vec_result);
        let dag = builder.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 3);
        add_scalar_input(&mut inputs, "b", 5);

        let result = execute_graph(&dag, inputs).unwrap();
        
        // Expected: [3+5, 3*5] = [8, 15]
        let expected = Value::value_vec(vec![scalar::<C>(8), scalar::<C>(15)]);

        assert!(
            values_equal(&result, &expected),
            "Multiple outputs should compute correctly"
        );
    }

    #[test]
    fn test_shared_subexpression() {
        // Test: a*b appears in both (a*b)+c and (a*b)*d
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());
        let b = builder.add_input("b", ATyp::scalar());
        let c = builder.add_input("c", ATyp::scalar());
        let d = builder.add_input("d", ATyp::scalar());
        
        // Compute a*b once
        let ab = Op::mul(
            Op::Ref(a.clone(), ATyp::scalar()),
            Op::Ref(b.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder.add_op(ab);
        
        // Use it in two places
        let ab_plus_c = Op::add(
            Op::Ref(ab_ref.clone(), ATyp::scalar()),
            Op::Ref(c.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let left_ref = builder.add_op(ab_plus_c);
        
        let ab_times_d = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(d.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        let right_ref = builder.add_op(ab_times_d);
        
        // Final result: (a*b+c) * (a*b*d)
        let final_result = Op::mul(
            Op::Ref(left_ref, ATyp::scalar()),
            Op::Ref(right_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(final_result);
        let dag = builder.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 2);
        add_scalar_input(&mut inputs, "b", 3);
        add_scalar_input(&mut inputs, "c", 1);
        add_scalar_input(&mut inputs, "d", 4);

        let result = execute_graph(&dag, inputs).unwrap();
        // a*b = 6, a*b+c = 7, a*b*d = 24, final = 7*24 = 168
        let expected = scalar::<C>(168);

        assert!(
            values_equal(&result, &expected),
            "Shared subexpression should work correctly"
        );
    }

    #[test]
    fn test_vector_element_operations() {
        // Create a vector, then do operations on its elements conceptually
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());
        let b = builder.add_input("b", ATyp::scalar());
        let c = builder.add_input("c", ATyp::scalar());
        
        // Create vector [a, b]
        let vec1 = Op::vec(vec![
            Op::Ref(a.clone(), ATyp::scalar()),
            Op::Ref(b.clone(), ATyp::scalar()),
        ]);
        
        // Multiply vector by scalar c
        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let scaled = Op::mul(Op::Ref(c.clone(), ATyp::scalar()), vec1, vec_typ);
        builder.add_op(scaled);
        let dag = builder.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 2);
        add_scalar_input(&mut inputs, "b", 3);
        add_scalar_input(&mut inputs, "c", 5);

        let result = execute_graph(&dag, inputs).unwrap();
        // Expected: [2*5, 3*5] = [10, 15]
        let expected = Value::value_vec(vec![scalar::<C>(10), scalar::<C>(15)]);

        assert!(
            values_equal(&result, &expected),
            "Vector element operations should work"
        );
    }

    #[test]
    fn test_zero_simplifications_in_complex_expr() {
        // Test that 0 simplifications work in complex expressions: (a + 0) * (b + 0)
        let mut builder = GraphBuilder::<C>::new();
        let a = builder.add_input("a", ATyp::scalar());
        let b = builder.add_input("b", ATyp::scalar());
        
        let a_plus_0 = Op::add(
            Op::Ref(a.clone(), ATyp::scalar()),
            Op::Value(zero_scalar()),
            ATyp::scalar(),
        );
        // This should simplify to just a
        let a_ref = builder.add_op(a_plus_0);
        
        let b_plus_0 = Op::add(
            Op::Ref(b.clone(), ATyp::scalar()),
            Op::Value(zero_scalar()),
            ATyp::scalar(),
        );
        // This should simplify to just b
        let b_ref = builder.add_op(b_plus_0);
        
        let result = Op::mul(
            Op::Ref(a_ref, ATyp::scalar()),
            Op::Ref(b_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(result);
        let dag = builder.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 7);
        add_scalar_input(&mut inputs, "b", 11);

        let result = execute_graph(&dag, inputs).unwrap();
        let expected = scalar::<C>(77); // 7 * 11

        assert!(
            values_equal(&result, &expected),
            "Zero simplifications should work in complex expressions"
        );
    }
}
