/// Tests for polynomial ring laws and algebraic properties end-to-end through graph operations
use crate::{Op, mk};
use backend::{ArkBn254, Value, PolyVariant, ATyp, VirtualPolynomial};
use ark_poly::{
    univariate::DensePolynomial,
    DenseUVPolynomial,
};
use std::collections::HashMap;
use crate::eval::eval_op;

type TestValue = Value<ArkBn254>;
type Fr = <ArkBn254 as backend::ArkConfig>::F;

fn make_scalar(val: u64) -> TestValue {
    TestValue::Poly(VirtualPolynomial::from_poly(PolyVariant::from_scalar(Fr::from(val))))
}

fn make_uni_poly(coeffs: Vec<u64>) -> TestValue {
    let poly = DensePolynomial::from_coefficients_vec(
        coeffs.into_iter().map(Fr::from).collect()
    );
    TestValue::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(poly)))
}

#[test]
fn test_addition_commutative() {
    let p1 = make_uni_poly(vec![1, 2, 3]); // 1 + 2x + 3x^2
    let p2 = make_uni_poly(vec![4, 5]);    // 4 + 5x

    let op1 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );

    let op2 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p2.clone())),
        mk::<ArkBn254>(Op::Value(p1.clone())),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result1 = eval_op(&mk::<ArkBn254>(op1), &env).unwrap();
    let result2 = eval_op(&mk::<ArkBn254>(op2), &env).unwrap();

    assert_eq!(result1, result2, "Addition should be commutative");
}

#[test]
fn test_addition_associative() {
    let p1 = make_uni_poly(vec![1, 2]);
    let p2 = make_uni_poly(vec![3, 4]);
    let p3 = make_uni_poly(vec![5, 6]);

    // (p1 + p2) + p3
    let inner1 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );
    let op1 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(inner1),
        mk::<ArkBn254>(Op::Value(p3.clone())),
        ATyp::Uni(10)
    );

    // p1 + (p2 + p3)
    let inner2 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p2.clone())),
        mk::<ArkBn254>(Op::Value(p3.clone())),
        ATyp::Uni(10)
    );
    let op2 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(inner2),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result1 = eval_op(&mk::<ArkBn254>(op1), &env).unwrap();
    let result2 = eval_op(&mk::<ArkBn254>(op2), &env).unwrap();

    assert_eq!(result1, result2, "Addition should be associative");
}

#[test]
fn test_addition_identity() {
    let p = make_uni_poly(vec![1, 2, 3]);
    let zero = make_scalar(0);

    let op = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p.clone())),
        mk::<ArkBn254>(Op::Value(zero)),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result = eval_op(&mk::<ArkBn254>(op), &env).unwrap();

    assert_eq!(result, p, "Adding zero should be identity");
}

#[test]
fn test_multiplication_commutative() {
    let p1 = make_uni_poly(vec![1, 2]); // 1 + 2x
    let p2 = make_uni_poly(vec![3, 4]); // 3 + 4x

    let op1 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );

    let op2 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p2.clone())),
        mk::<ArkBn254>(Op::Value(p1.clone())),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result1 = eval_op(&mk::<ArkBn254>(op1), &env).unwrap();
    let result2 = eval_op(&mk::<ArkBn254>(op2), &env).unwrap();

    assert_eq!(result1, result2, "Multiplication should be commutative");
}

#[test]
fn test_multiplication_associative() {
    let p1 = make_uni_poly(vec![1, 1]); // 1 + x
    let p2 = make_uni_poly(vec![2, 1]); // 2 + x
    let p3 = make_uni_poly(vec![3, 1]); // 3 + x

    // (p1 * p2) * p3
    let inner1 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );
    let op1 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(inner1),
        mk::<ArkBn254>(Op::Value(p3.clone())),
        ATyp::Uni(10)
    );

    // p1 * (p2 * p3)
    let inner2 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p2.clone())),
        mk::<ArkBn254>(Op::Value(p3.clone())),
        ATyp::Uni(10)
    );
    let op2 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(inner2),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result1 = eval_op(&mk::<ArkBn254>(op1), &env).unwrap();
    let result2 = eval_op(&mk::<ArkBn254>(op2), &env).unwrap();

    assert_eq!(result1, result2, "Multiplication should be associative");
}

#[test]
fn test_multiplication_identity() {
    let p = make_uni_poly(vec![1, 2, 3]);
    let one = make_scalar(1);

    let op = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p.clone())),
        mk::<ArkBn254>(Op::Value(one)),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result = eval_op(&mk::<ArkBn254>(op), &env).unwrap();

    assert_eq!(result, p, "Multiplying by one should be identity");
}

#[test]
fn test_distributivity() {
    let p1 = make_uni_poly(vec![1, 2]); // 1 + 2x
    let p2 = make_uni_poly(vec![3, 4]); // 3 + 4x
    let p3 = make_uni_poly(vec![5, 6]); // 5 + 6x

    // p1 * (p2 + p3)
    let inner_add = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p2.clone())),
        mk::<ArkBn254>(Op::Value(p3.clone())),
        ATyp::Uni(10)
    );
    let op1 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(inner_add),
        ATyp::Uni(10)
    );

    // (p1 * p2) + (p1 * p3)
    let mul1 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );
    let mul2 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p3.clone())),
        ATyp::Uni(10)
    );
    let op2 = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(mul1),
        mk::<ArkBn254>(mul2),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result1 = eval_op(&mk::<ArkBn254>(op1), &env).unwrap();
    let result2 = eval_op(&mk::<ArkBn254>(op2), &env).unwrap();

    assert_eq!(result1, result2, "Multiplication should distribute over addition");
}

#[test]
fn test_scalar_multiplication_compatibility() {
    let p = make_uni_poly(vec![2, 3]); // 2 + 3x
    let s1 = make_scalar(4);
    let s2 = make_scalar(5);

    // (s1 * s2) * p
    let scalar_mul = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(s1.clone())),
        mk::<ArkBn254>(Op::Value(s2.clone())),
        ATyp::Uni(10)
    );
    let op1 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(scalar_mul),
        mk::<ArkBn254>(Op::Value(p.clone())),
        ATyp::Uni(10)
    );

    // s1 * (s2 * p)
    let inner_mul = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(s2.clone())),
        mk::<ArkBn254>(Op::Value(p.clone())),
        ATyp::Uni(10)
    );
    let op2 = Op::Bin(
        lang::ast::BinOp::Mul,
        mk::<ArkBn254>(Op::Value(s1.clone())),
        mk::<ArkBn254>(inner_mul),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result1 = eval_op(&mk::<ArkBn254>(op1), &env).unwrap();
    let result2 = eval_op(&mk::<ArkBn254>(op2), &env).unwrap();

    assert_eq!(result1, result2, "Scalar multiplication should be compatible");
}

#[test]
fn test_subtraction_as_addition_of_negation() {
    let p1 = make_uni_poly(vec![5, 6]);
    let p2 = make_uni_poly(vec![2, 3]);

    // p1 - p2
    let sub_op = Op::Bin(
        lang::ast::BinOp::Sub,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );

    // p1 + (-1 * p2) = p1 + (neg p2)
    // In field arithmetic, -p2 is just negation
    let neg_p2 = Op::Bin(
        lang::ast::BinOp::Sub,
        mk::<ArkBn254>(Op::Value(make_scalar(0))),
        mk::<ArkBn254>(Op::Value(p2.clone())),
        ATyp::Uni(10)
    );
    let add_op = Op::Bin(
        lang::ast::BinOp::Add,
        mk::<ArkBn254>(Op::Value(p1.clone())),
        mk::<ArkBn254>(neg_p2),
        ATyp::Uni(10)
    );

    let env = HashMap::new();
    let result_sub = eval_op(&mk::<ArkBn254>(sub_op), &env).unwrap();
    let result_add = eval_op(&mk::<ArkBn254>(add_op), &env).unwrap();

    assert_eq!(result_sub, result_add, "Subtraction should equal addition of negation");
}
