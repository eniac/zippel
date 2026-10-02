//! Basic Operation Tests
//!
//! This module tests individual graph operation constructors
//! and basic functionality.

#[cfg(test)]
mod op_construction {
    use crate::tests::test_helpers::*;
    use crate::{GOp, Op};
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

        let op: GOp<C> = Op::add(Op::Value(zero), Op::Value(v.clone()), ATyp::scalar());

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

        let op: GOp<C> = Op::add(Op::Value(v.clone()), Op::Value(zero), ATyp::scalar());

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

        let op: GOp<C> = Op::add(Op::Value(v1), Op::Value(v2), ATyp::scalar());

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

        let op: GOp<C> = Op::sub(Op::Value(v.clone()), Op::Value(zero), ATyp::scalar());

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

        let op: GOp<C> = Op::sub(Op::Value(v1), Op::Value(v2), ATyp::scalar());

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

        let op: GOp<C> = Op::mul(Op::Value(zero.clone()), Op::Value(v), ATyp::scalar());

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

        let op: GOp<C> = Op::mul(Op::Value(v), Op::Value(zero.clone()), ATyp::scalar());

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

        let op: GOp<C> = Op::mul(Op::Value(one), Op::Value(v.clone()), ATyp::scalar());

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

        let op: GOp<C> = Op::mul(Op::Value(v.clone()), Op::Value(one), ATyp::scalar());

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

        let op: GOp<C> = Op::mul(Op::Value(v1), Op::Value(v2), ATyp::scalar());

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

        let op: GOp<C> = Op::div(Op::Value(zero.clone()), Op::Value(v), ATyp::scalar());

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

        let op: GOp<C> = Op::div(Op::Value(v.clone()), Op::Value(one), ATyp::scalar());

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

        let op: GOp<C> = Op::div(Op::Value(v1), Op::Value(v2), ATyp::scalar());

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

        let _op: GOp<C> = Op::div(Op::Value(v), Op::Value(zero), ATyp::scalar());
    }

    // ============================================================================
    // VECTOR OPERATIONS
    // ============================================================================

    #[test]
    fn test_op_vec_construction() {
        let v1 = scalar::<C>(1);
        let v2 = scalar::<C>(2);
        let v3 = scalar::<C>(3);

        let op: GOp<C> = Op::vec(vec![Op::Value(v1), Op::Value(v2), Op::Value(v3)]);

        match op {
            Op::Vec(elements) => assert_eq!(elements.len(), 3),
            _ => panic!("Expected Vec operation"),
        }
    }

    #[test]
    fn test_op_vec_add() {
        let vec1 = Op::vec(vec![Op::Value(scalar::<C>(1)), Op::Value(scalar::<C>(2))]);

        let vec2 = Op::vec(vec![Op::Value(scalar::<C>(3)), Op::Value(scalar::<C>(4))]);

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
        let vec = Op::vec(vec![Op::Value(scalar::<C>(3)), Op::Value(scalar::<C>(4))]);

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
        let vec1 = Op::vec(vec![Op::Value(scalar::<C>(1)), Op::Value(scalar::<C>(2))]);

        let vec2 = Op::vec(vec![Op::Value(scalar::<C>(3)), Op::Value(scalar::<C>(4))]);

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
    use crate::Op;
    use crate::tests::test_helpers::*;
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
            Op::Ref(a, ATyp::scalar()),
            Op::Ref(b, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder.add_op(ab);

        let abc = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(c, ATyp::scalar()),
            ATyp::scalar(),
        );
        let abc_ref = builder.add_op(abc);

        let result = Op::sub(
            Op::Ref(abc_ref, ATyp::scalar()),
            Op::Ref(d, ATyp::scalar()),
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
            Op::Ref(a, ATyp::scalar()),
            Op::Ref(b, ATyp::scalar()),
            ATyp::scalar(),
        );
        let add_ref = builder.add_op(add_result);

        let mul_result = Op::mul(
            Op::Ref(a, ATyp::scalar()),
            Op::Ref(b, ATyp::scalar()),
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
            Op::Ref(a, ATyp::scalar()),
            Op::Ref(b, ATyp::scalar()),
            ATyp::scalar(),
        );
        let ab_ref = builder.add_op(ab);

        // Use it in two places
        let ab_plus_c = Op::add(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(c, ATyp::scalar()),
            ATyp::scalar(),
        );
        let left_ref = builder.add_op(ab_plus_c);

        let ab_times_d = Op::mul(
            Op::Ref(ab_ref, ATyp::scalar()),
            Op::Ref(d, ATyp::scalar()),
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
        let vec1 = Op::vec(vec![Op::Ref(a, ATyp::scalar()), Op::Ref(b, ATyp::scalar())]);

        // Multiply vector by scalar c
        let vec_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let scaled = Op::mul(Op::Ref(c, ATyp::scalar()), vec1, vec_typ);
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
            Op::Ref(a, ATyp::scalar()),
            Op::Value(zero_scalar()),
            ATyp::scalar(),
        );
        // This should simplify to just a
        let a_ref = builder.add_op(a_plus_0);

        let b_plus_0 = Op::add(
            Op::Ref(b, ATyp::scalar()),
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

    // ── Numeric literals in a field ─────────────────────────────────────

    /// A literal above `u64::MAX` and both test moduli.
    const BIG: &str = "34545435435435435435435";

    /// Lowers `src` and runs its function `name` on `inputs`.
    fn run<B: crate::HasOpFactory>(
        src: &str,
        name: &str,
        inputs: share::Ctx<lang::id::Vid, Value<B>>,
    ) -> Value<B> {
        let module = parse_and_concretize(src, &share::Ctx::new());
        let dags = crate::UDags::<B>::from_module(module).unwrap();
        let dag = dags
            .functions()
            .into_iter()
            .find(|dag| dag.name() == lang::id::Vid::from(name))
            .unwrap_or_else(|| panic!("no function `{name}`"));
        execute_graph(dag, inputs).unwrap()
    }

    /// `n` in the field of `B`.
    fn f<B: backend::ArkConfig>(n: u64) -> <B as backend::ArkConfig>::F {
        n.into()
    }

    /// `got` is the field element `expected` (not an index of the same value).
    #[track_caller]
    fn assert_field<B: backend::ArkConfig>(got: &Value<B>, expected: <B as backend::ArkConfig>::F) {
        assert!(
            matches!(got, Value::Scalar(x) if *x == expected),
            "expected Scalar({expected}), got {got}"
        );
    }

    /// `got` is the field vector `expected`.
    #[track_caller]
    fn assert_fields<B: backend::ArkConfig>(got: &Value<B>, expected: &[u64]) {
        let expected: Vec<_> = expected.iter().map(|&n| f::<B>(n)).collect();
        assert!(
            matches!(got, Value::VecScalar(xs) if *xs == expected),
            "expected VecScalar({expected:?}), got {got}"
        );
    }

    fn literal_modulo_field<B: crate::HasOpFactory>(residue: u64) {
        let src = format!("fn f<F: Field>() -> F {{ {BIG} }}");
        assert_field::<B>(&run::<B>(&src, "f", share::Ctx::new()), f::<B>(residue));
    }

    #[test]
    fn numeric_literal_modulo_field() {
        literal_modulo_field::<backend::ArkField17>(14);
        literal_modulo_field::<backend::ArkField65537>(55512);
        // A finite literal returned as a field element is reduced, not an index.
        type B = backend::ArkField17;
        let got = run::<B>("fn f<F: Field>() -> F { 18 }", "f", share::Ctx::new());
        assert_field::<B>(&got, f::<B>(1));
    }

    #[test]
    fn numeric_literal_field_uses() {
        type B = backend::ArkField17;
        let none = share::Ctx::new;
        let scalar_of = |src: &str| run::<B>(src, "f", none());

        assert_field::<B>(
            &scalar_of("fn f<F: Field>() -> F { let one = 1; one }"),
            f::<B>(1),
        );
        assert_fields::<B>(&scalar_of("fn f<F: Field>() -> [F; 2] { [1, 2] }"), &[1, 2]);
        assert_field::<B>(
            &scalar_of(
                "fn g<F: Field>(instance x: F) -> F { x }
                 fn f<F: Field>() -> F { g(1) }",
            ),
            f::<B>(1),
        );
        assert_field::<B>(&scalar_of("fn f<F: Field>() -> F { -1 }"), -f::<B>(1));
        // 19 exceeds the modulus 17: field uses reduce it to 2.
        assert_field::<B>(&scalar_of("fn f<F: Field>() -> F { -19 }"), f::<B>(15));
        assert_fields::<B>(
            &scalar_of("fn f<F: Field>() -> [F; 2] { [19 for i in 0..2] }"),
            &[2, 2],
        );
        assert_field::<B>(
            &scalar_of(
                "fn f<F: Field>() -> F {
                     let pts = [0, 1, 2];
                     let p = interpolate(pts, [1, 2, 3]);
                     p(1)
                 }",
            ),
            f::<B>(2),
        );

        // A finite index still selects; an uppercase size is a literal, not a shape.
        let mut xs = share::Ctx::new();
        xs.insert(
            &lang::id::Vid::from("xs"),
            &Value::VecScalar(vec![f::<B>(5), f::<B>(7)]),
        );
        let got = run::<B>(
            "fn f<F: Field>(instance xs: [F; 2]) -> F { xs[1] }",
            "f",
            xs,
        );
        assert_field::<B>(&got, f::<B>(7));
        let mut xs = share::Ctx::new();
        let mut elems = vec![f::<B>(0); 7];
        elems[0] = f::<B>(3);
        xs.insert(&lang::id::Vid::from("xs"), &Value::VecScalar(elems));
        let got = run::<B>(
            "fn f<N: 7, F: Field>(instance xs: [F; N]) -> F { xs[0] + N }",
            "f",
            xs,
        );
        assert_field::<B>(&got, f::<B>(10));

        // Literals in `fun` bodies are field constants in the fun's own encoding.
        let fun_at = |fun: &str, point: &str| {
            scalar_of(&format!(
                "fn f<F: Field>() -> F {{ let p = ({fun}); eval(p, {point}) }}"
            ))
        };
        assert_field::<B>(&fun_at("fun(x) => 19 + x", "0"), f::<B>(2));
        assert_field::<B>(&fun_at("fun(x, y) => 19", "[0, 0]"), f::<B>(2));
        assert_field::<B>(&fun_at("fun(x, y) => -1", "[0, 0]"), f::<B>(16));
        assert_field::<B>(&fun_at("fun(x, y) => 19 * 2", "[0, 0]"), f::<B>(4));
        assert_field::<B>(&fun_at("fun(x, y) => 19 * x", "[1, 0]"), f::<B>(2));
        assert_field::<B>(&fun_at("fun(x, y) => (19 + 1) * x", "[1, 0]"), f::<B>(3));
        let module = parse_and_concretize(
            "fn f<F: Field>() -> F { let p = (fun(x, y) => x * x); eval(p, [0, 0]) }",
            &share::Ctx::new(),
        );
        assert!(matches!(
            crate::UDags::<B>::from_module(module),
            Err(crate::GraphError::NonPolynomialFun(..))
        ));

        // A polynomial plus a literal keeps its polynomial type even when the sum folds.
        assert_field::<B>(
            &scalar_of("fn f<F: Field>() -> F { let p = (fun(x) => 0); let q = p + 17; q(0) }"),
            f::<B>(0),
        );
    }

    /// An integer stored into a field of a record becomes a field element of that field.
    #[test]
    fn numeric_literal_record_update() {
        type B = backend::ArkField17;
        let src = "proto p<F: Field>(instance r: {a: F}) where r.a == r.a {
                       s <- r.set(a, 18);
                       verify(s.a == 1)
                   }";
        let module = parse_and_concretize(src, &share::Ctx::new());
        let dags = crate::UDags::<B>::from_module(module).unwrap();
        let dag = dags.protocols()[0];
        let mut inputs = share::Ctx::new();
        inputs.insert(
            &lang::id::Vid::from("r"),
            &Value::Record(share::Ctx::from_iter([(
                "a".to_string(),
                Value::Scalar(f::<B>(9)),
            )])),
        );
        let values = execute_graph_all(dag, inputs);
        let s = values
            .iter()
            .find(|(n, _)| {
                dag.binding(**n)
                    .is_some_and(|b| b.node == lang::id::Vid::from("s"))
            })
            .map(|(_, v)| v)
            .expect("`s` is logged");
        let Value::Record(fields) = s else {
            panic!("`s` is a record, got {s}")
        };
        assert_field::<B>(&fields[&"a".to_string()], f::<B>(1));
    }
}
