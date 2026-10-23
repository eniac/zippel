use super::*;
use crate::ArkBn254;
use crate::poly::variant::{DenseMle, DenseUni, PolyVariant};
use crate::poly::virtual_polynomial::VirtualPolynomial;
use crate::{ATyp, DivisionByZero, Field, Group};
use ark_bn254::{Fr, G1Projective, G2Projective};
use lang::ast::{BinOp, Exclusion};
use rand::thread_rng;

type TestConfig = ArkBn254;
type TestValue = Value<TestConfig>;

// Helper to create test values
fn scalar(x: u64) -> TestValue {
    TestValue::Scalar(Fr::from(x))
}

fn vec_scalar(xs: &[u64]) -> TestValue {
    TestValue::vec_scalar(xs.iter().map(|&x| Fr::from(x)).collect())
}

fn random_scalar() -> TestValue {
    TestValue::Scalar(Fr::rand(&mut thread_rng()))
}

fn random_g1() -> TestValue {
    TestValue::g1(G1Projective::rand(&mut thread_rng()))
}

fn random_g2() -> TestValue {
    TestValue::G2(G2Projective::rand(&mut thread_rng()).into())
}

// Helper trait to extract inner values
trait IntoG1 {
    fn into_g1(self) -> G1Projective;
}

trait IntoG2 {
    fn into_g2(self) -> G2Projective;
}

impl IntoG1 for TestValue {
    fn into_g1(self) -> G1Projective {
        match self {
            TestValue::G1(g) => *g,
            _ => panic!("Expected G1"),
        }
    }
}

impl IntoG2 for TestValue {
    fn into_g2(self) -> G2Projective {
        match self {
            TestValue::G2(g) => *g,
            _ => panic!("Expected G2"),
        }
    }
}

// ========== Addition Laws ==========

#[test]
fn test_scalar_add_associativity() {
    let a = scalar(5);
    let b = scalar(7);
    let c = scalar(11);
    assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
}

#[test]
fn test_scalar_add_commutativity() {
    let a = scalar(5);
    let b = scalar(7);
    assert_eq!(a.clone() + b.clone(), b + a);
}

#[test]
fn test_scalar_add_identity() {
    let a = scalar(5);
    let zero = scalar(0);
    assert_eq!(a.clone() + zero.clone(), a.clone());
    assert_eq!(zero + a.clone(), a);
}

#[test]
fn test_vec_scalar_add_associativity() {
    let a = vec_scalar(&[1, 2, 3]);
    let b = vec_scalar(&[4, 5, 6]);
    let c = vec_scalar(&[7, 8, 9]);
    assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
}

#[test]
fn test_vec_scalar_add_commutativity() {
    let a = vec_scalar(&[1, 2, 3]);
    let b = vec_scalar(&[4, 5, 6]);
    assert_eq!(a.clone() + b.clone(), b + a);
}

#[test]
fn test_g1_add_associativity() {
    let a = random_g1();
    let b = random_g1();
    let c = random_g1();
    assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
}

#[test]
fn test_g1_add_commutativity() {
    let a = random_g1();
    let b = random_g1();
    assert_eq!(a.clone() + b.clone(), b + a);
}

#[test]
fn test_g2_add_associativity() {
    let a = random_g2();
    let b = random_g2();
    let c = random_g2();
    assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
}

#[test]
fn test_g2_add_commutativity() {
    let a = random_g2();
    let b = random_g2();
    assert_eq!(a.clone() + b.clone(), b + a);
}

// ========== Multiplication Laws ==========

#[test]
fn test_scalar_mul_associativity() {
    let a = scalar(5);
    let b = scalar(7);
    let c = scalar(11);
    assert_eq!((a.clone() * b.clone()) * c.clone(), a * (b * c));
}

#[test]
fn test_scalar_mul_commutativity() {
    let a = scalar(5);
    let b = scalar(7);
    assert_eq!(a.clone() * b.clone(), b * a);
}

#[test]
fn test_scalar_mul_identity() {
    let a = scalar(5);
    let one = scalar(1);
    assert_eq!(a.clone() * one.clone(), a.clone());
    assert_eq!(one * a.clone(), a);
}

#[test]
fn test_scalar_mul_zero() {
    let a = scalar(5);
    let zero = scalar(0);
    assert_eq!(a * zero, scalar(0));
}

#[test]
fn test_vec_scalar_mul_commutativity() {
    let a = vec_scalar(&[1, 2, 3]);
    let b = vec_scalar(&[4, 5, 6]);
    assert_eq!(a.clone() * b.clone(), b * a);
}

// ========== Distributivity Laws ==========

#[test]
fn test_scalar_distributivity_left() {
    let a = scalar(5);
    let b = scalar(7);
    let c = scalar(11);
    assert_eq!(
        a.clone() * (b.clone() + c.clone()),
        (a.clone() * b) + (a * c)
    );
}

#[test]
fn test_scalar_distributivity_right() {
    let a = scalar(5);
    let b = scalar(7);
    let c = scalar(11);
    assert_eq!(
        (a.clone() + b.clone()) * c.clone(),
        (a * c.clone()) + (b * c)
    );
}

#[test]
fn test_vec_scalar_distributivity_left() {
    let a = vec_scalar(&[1, 2, 3]);
    let b = vec_scalar(&[4, 5, 6]);
    let c = vec_scalar(&[7, 8, 9]);
    assert_eq!(
        a.clone() * (b.clone() + c.clone()),
        (a.clone() * b) + (a * c)
    );
}

#[test]
fn test_vec_scalar_distributivity_right() {
    let a = vec_scalar(&[1, 2, 3]);
    let b = vec_scalar(&[4, 5, 6]);
    let c = vec_scalar(&[7, 8, 9]);
    assert_eq!(
        (a.clone() + b.clone()) * c.clone(),
        (a * c.clone()) + (b * c)
    );
}

// ========== Subtraction Laws ==========

#[test]
fn test_scalar_sub_identity() {
    let a = scalar(5);
    assert_eq!(a.clone() - a, scalar(0));
}

#[test]
fn test_vec_scalar_sub_identity() {
    let a = vec_scalar(&[1, 2, 3]);
    assert_eq!(a.clone() - a, vec_scalar(&[0, 0, 0]));
}

// ========== Scalar Multiplication (Group Action) ==========

#[test]
fn test_g1_scalar_mul_distributivity_scalars() {
    let g = random_g1();
    let a = random_scalar();
    let b = random_scalar();

    // (a + b) * G = a * G + b * G
    let lhs = (a.clone() + b.clone()) * g.clone();
    let rhs = (a * g.clone()) + (b * g);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g1_scalar_mul_distributivity_points() {
    let g1 = random_g1();
    let g2 = random_g1();
    let a = random_scalar();

    // a * (G1 + G2) = a * G1 + a * G2
    let lhs = a.clone() * (g1.clone() + g2.clone());
    let rhs = (a.clone() * g1) + (a * g2);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g2_scalar_mul_distributivity_scalars() {
    let g = random_g2();
    let a = random_scalar();
    let b = random_scalar();

    // (a + b) * G = a * G + b * G
    let lhs = (a.clone() + b.clone()) * g.clone();
    let rhs = (a * g.clone()) + (b * g);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g2_scalar_mul_distributivity_points() {
    let g1 = random_g2();
    let g2 = random_g2();
    let a = random_scalar();

    // a * (G1 + G2) = a * G1 + a * G2
    let lhs = a.clone() * (g1.clone() + g2.clone());
    let rhs = (a.clone() * g1) + (a * g2);
    assert_eq!(lhs, rhs);
}

// ========== Index Operations ==========

#[test]
fn test_index_add() {
    let a = TestValue::Index(5);
    let b = TestValue::Index(7);
    assert_eq!(a + b, TestValue::Index(12));
}

#[test]
fn test_index_mul() {
    let a = TestValue::Index(5);
    let b = TestValue::Index(7);
    assert_eq!(a * b, TestValue::Index(35));
}

#[test]
fn test_vec_index_add() {
    let a = TestValue::VecIndex(vec![1, 2, 3].into());
    let b = TestValue::VecIndex(vec![4, 5, 6].into());
    assert_eq!(a + b, TestValue::VecIndex(vec![5, 7, 9].into()));
}

// ========== Field Axioms for Division ==========

#[test]
fn test_scalar_div_mul_identity() {
    // (a / b) * b = a (when b ≠ 0)
    let a = scalar(42);
    let b = scalar(7);
    let result = (a.clone() / b.clone()) * b;
    assert_eq!(result, a);
}

#[test]
fn test_scalar_multiplicative_inverse() {
    // a * (1/a) = 1 (when a ≠ 0)
    let a = scalar(5);
    let one = scalar(1);
    let a_inv = one.clone() / a.clone();
    assert_eq!(a * a_inv, one);
}

#[test]
fn test_scalar_div_by_zero_fails() {
    assert_eq!(
        scalar(1).value_bin(BinOp::Div, scalar(0)),
        Err(DivisionByZero)
    );
}

#[test]
fn test_vec_scalar_div_by_a_zero_entry_fails() {
    let a = TestValue::vec_scalar(vec![Fr::from(1u64), Fr::from(2u64)]);
    let b = TestValue::vec_scalar(vec![Fr::from(1u64), Fr::from(0u64)]);
    assert_eq!(a.value_bin(BinOp::Div, b), Err(DivisionByZero));
}

/// A sample is excluded when it is listed (`[0]` for a nonzero sample),
/// or a root of unity of the given order.
#[test]
fn test_is_excluded_by() {
    let minus_one = TestValue::Scalar(-Fr::from(1u64));
    let listed = Exclusion::Values(TestValue::vec_scalar(vec![Fr::from(2u64), Fr::from(3u64)]));
    let zero = Exclusion::Values(TestValue::vec_scalar(vec![Fr::from(0u64)]));
    assert!(scalar(0).is_excluded_by(&zero));
    assert!(!scalar(1).is_excluded_by(&zero));
    assert!(scalar(3).is_excluded_by(&listed));
    assert!(!scalar(4).is_excluded_by(&listed));
    assert!(scalar(1).is_excluded_by(&Exclusion::RootsOfUnity(4)));
    assert!(minus_one.is_excluded_by(&Exclusion::RootsOfUnity(4)));
    assert!(!minus_one.is_excluded_by(&Exclusion::RootsOfUnity(3)));
    assert!(!scalar(2).is_excluded_by(&Exclusion::RootsOfUnity(4)));
}

#[test]
fn test_scalar_div_by_one() {
    // a / 1 = a
    let a = scalar(42);
    let one = scalar(1);
    assert_eq!(a.clone() / one, a);
}

#[test]
fn test_scalar_div_self() {
    // a / a = 1 (when a ≠ 0)
    let a = scalar(7);
    assert_eq!(a.clone() / a, scalar(1));
}

#[test]
fn test_vec_scalar_div_consistency() {
    // Division of vectors should be element-wise
    let a = vec_scalar(&[10, 20, 30]);
    let b = vec_scalar(&[2, 4, 5]);
    let result = a / b;
    assert_eq!(result, vec_scalar(&[5, 5, 6]));
}

#[test]
fn test_index_div() {
    // Index / Index = Index
    let a = TestValue::Index(42);
    let b = TestValue::Index(7);
    assert_eq!(a / b, TestValue::Index(6));
}

#[test]
fn test_index_coerce_div() {
    // Index should coerce to scalar in division
    let a = TestValue::Index(10);
    let b = scalar(2);
    let result = a / b;
    assert_eq!(result, scalar(5));
}

#[test]
fn test_vec_index_div() {
    let a = TestValue::VecIndex(vec![10, 20, 30].into());
    let b = TestValue::VecIndex(vec![2, 4, 5].into());
    assert_eq!(a / b, TestValue::VecIndex(vec![5, 5, 6].into()));
}

// ========== Group Identity Elements ==========

#[test]
fn test_g1_additive_identity() {
    let a = random_g1();
    let zero = TestValue::g1(G1Projective::zero());
    assert_eq!(a.clone() + zero.clone(), a.clone());
    assert_eq!(zero + a.clone(), a);
}

#[test]
fn test_g2_additive_identity() {
    let a = random_g2();
    let zero = TestValue::G2(G2Projective::zero().into());
    assert_eq!(a.clone() + zero.clone(), a.clone());
    assert_eq!(zero + a.clone(), a);
}

#[test]
fn test_value_dot_vec_g1_vec_g2_returns_aggregate_gt_and_pair_returns_vecgt() {
    use ark_ec::pairing::Pairing as _;
    let g1 = vec![
        G1Projective::rand(&mut thread_rng()),
        G1Projective::rand(&mut thread_rng()),
    ];
    let g2 = vec![
        G2Projective::rand(&mut thread_rng()),
        G2Projective::rand(&mut thread_rng()),
    ];

    let dot = TestValue::vec_g1(g1.clone()).dot(TestValue::vec_g2(g2.clone()));
    let reference = ark_bn254::Bn254::multi_pairing(g1.iter().copied(), g2.iter().copied());
    assert_eq!(dot, TestValue::GT(reference.into()));

    let reverse_dot = TestValue::vec_g2(g2.clone()).dot(TestValue::vec_g1(g1.clone()));
    assert_eq!(reverse_dot, TestValue::GT(reference.into()));

    let pair = TestValue::vec_g1(g1).pair(TestValue::vec_g2(g2));
    assert!(matches!(pair, TestValue::VecGT(v) if v.len() == 2));
}

#[test]
fn test_gt_additive_identity() {
    use ark_ec::pairing::Pairing as _;
    let a_g1 = random_g1();
    let a_g2 = random_g2();
    let mut a = a_g2.clone();
    a_g1.value_pair(&mut a);

    let b_g1 = random_g1();
    let b_g2 = random_g2();
    let mut b = b_g2.clone();
    b_g1.value_pair(&mut b);

    // Test GT identity (zero in multiplicative group)
    let zero_gt =
        TestValue::GT(ark_bn254::Bn254::pairing(G1Projective::zero(), G2Projective::zero()).into());

    // GT is multiplicative, so zero_gt acts as zero in addition
    let result = a.clone() + zero_gt.clone();
    assert_eq!(result, a);
}

// ========== Group Inverse Properties ==========

#[test]
fn test_g1_additive_inverse() {
    // a + (-a) = 0
    let a = random_g1();
    let result = a.clone() - a;
    let zero = TestValue::g1(G1Projective::zero());
    assert_eq!(result, zero);
}

#[test]
fn test_g2_additive_inverse() {
    // a + (-a) = 0
    let a = random_g2();
    let result = a.clone() - a;
    let zero = TestValue::G2(G2Projective::zero().into());
    assert_eq!(result, zero);
}

#[test]
fn test_scalar_additive_inverse() {
    // a + (-a) = 0
    let a = scalar(42);
    let result = a.clone() - a;
    assert_eq!(result, scalar(0));
}

#[test]
fn test_vec_scalar_additive_inverse() {
    let a = vec_scalar(&[1, 2, 3, 4]);
    let result = a.clone() - a;
    assert_eq!(result, vec_scalar(&[0, 0, 0, 0]));
}

// ========== Subtraction Anti-commutativity ==========

#[test]
fn test_scalar_sub_anticommutativity() {
    // a - b = -(b - a)
    let a = scalar(10);
    let b = scalar(3);
    let lhs = a.clone() - b.clone();
    let rhs = scalar(0) - (b - a);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_vec_scalar_sub_anticommutativity() {
    let a = vec_scalar(&[10, 20, 30]);
    let b = vec_scalar(&[3, 5, 7]);
    let lhs = a.clone() - b.clone();
    let rhs_temp = b - a;
    let zero = vec_scalar(&[0, 0, 0]);
    let rhs = zero - rhs_temp;
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g1_sub_anticommutativity() {
    let a = random_g1();
    let b = random_g1();
    let lhs = a.clone() - b.clone();
    let rhs_temp = b - a;
    let zero = TestValue::g1(G1Projective::zero());
    let rhs = zero - rhs_temp;
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g2_sub_anticommutativity() {
    let a = random_g2();
    let b = random_g2();
    let lhs = a.clone() - b.clone();
    let rhs_temp = b - a;
    let zero = TestValue::G2(G2Projective::zero().into());
    let rhs = zero - rhs_temp;
    assert_eq!(lhs, rhs);
}

// ========== Subtraction Relation to Addition ==========

#[test]
fn test_scalar_sub_as_neg_add() {
    // a - b = a + (-b), where -b = 0 - b
    let a = scalar(10);
    let b = scalar(3);
    let lhs = a.clone() - b.clone();
    let neg_b = scalar(0) - b;
    let rhs = a + neg_b;
    assert_eq!(lhs, rhs);
}

#[test]
fn test_vec_scalar_sub_as_neg_add() {
    let a = vec_scalar(&[10, 20, 30]);
    let b = vec_scalar(&[3, 5, 7]);
    let lhs = a.clone() - b.clone();
    let neg_b = vec_scalar(&[0, 0, 0]) - b;
    let rhs = a + neg_b;
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g1_sub_as_neg_add() {
    let a = random_g1();
    let b = random_g1();
    let lhs = a.clone() - b.clone();
    let neg_b = TestValue::g1(G1Projective::zero()) - b;
    let rhs = a + neg_b;
    assert_eq!(lhs, rhs);
}

// ========== Index Operations ==========

#[test]
fn test_index_sub() {
    let a = TestValue::Index(10);
    let b = TestValue::Index(3);
    assert_eq!(a - b, TestValue::Index(7));
}

#[test]
fn test_index_mul_associativity() {
    let a = TestValue::Index(2);
    let b = TestValue::Index(3);
    let c = TestValue::Index(5);
    assert_eq!((a.clone() * b.clone()) * c.clone(), a * (b * c));
}

#[test]
fn test_index_mul_commutativity() {
    let a = TestValue::Index(5);
    let b = TestValue::Index(7);
    assert_eq!(a.clone() * b.clone(), b * a);
}

#[test]
fn test_index_mul_identity() {
    let a = TestValue::Index(42);
    let one = TestValue::Index(1);
    assert_eq!(a.clone() * one.clone(), a.clone());
    assert_eq!(one * a.clone(), a);
}

#[test]
fn test_index_mul_zero() {
    let a = TestValue::Index(42);
    let zero = TestValue::Index(0);
    assert_eq!(a * zero, TestValue::Index(0));
}

#[test]
fn test_vec_index_sub() {
    let a = TestValue::VecIndex(vec![10, 20, 30].into());
    let b = TestValue::VecIndex(vec![3, 5, 7].into());
    assert_eq!(a - b, TestValue::VecIndex(vec![7, 15, 23].into()));
}

#[test]
fn test_vec_index_mul() {
    let a = TestValue::VecIndex(vec![2, 3, 4].into());
    let b = TestValue::VecIndex(vec![5, 6, 7].into());
    assert_eq!(a * b, TestValue::VecIndex(vec![10, 18, 28].into()));
}

// ========== Remainder Operations ==========

#[test]
fn test_index_rem() {
    let a = TestValue::Index(17);
    let b = TestValue::Index(5);
    assert_eq!(a % b, TestValue::Index(2));
}

#[test]
fn test_vec_index_rem() {
    let a = TestValue::VecIndex(vec![17, 23, 31].into());
    let b = TestValue::VecIndex(vec![5, 7, 10].into());
    assert_eq!(a % b, TestValue::VecIndex(vec![2, 2, 1].into()));
}

#[test]
fn test_index_rem_by_scalar() {
    let a = TestValue::VecIndex(vec![17, 23, 31].into());
    let b = TestValue::Index(5);
    assert_eq!(a % b, TestValue::VecIndex(vec![2, 3, 1].into()));
}

#[test]
fn test_scalar_rem_by_index() {
    let a = TestValue::Index(17);
    let b = TestValue::VecIndex(vec![5, 7, 10].into());
    assert_eq!(a % b, TestValue::VecIndex(vec![2, 3, 7].into()));
}

// ========== Mixed Operations: Index Coercion ==========

#[test]
fn test_index_scalar_add() {
    // Index should coerce to scalar
    let idx = TestValue::Index(5);
    let scal = scalar(7);
    let result = idx + scal;
    assert_eq!(result, scalar(12));
}

#[test]
fn test_scalar_index_add() {
    // scalar + index: index coerces to scalar
    let scal = scalar(7);
    let idx = TestValue::Index(5);
    let result = scal + idx;
    assert_eq!(result, scalar(12));
}

#[test]
fn test_index_scalar_mul() {
    let idx = TestValue::Index(5);
    let scal = scalar(7);
    let result = idx * scal;
    assert_eq!(result, scalar(35));
}

#[test]
fn test_index_scalar_sub() {
    let idx = TestValue::Index(10);
    let scal = scalar(3);
    let result = idx - scal;
    assert_eq!(result, scalar(7));
}

#[test]
fn test_scalar_index_sub() {
    // scalar - index: index coerces to scalar
    let scal = scalar(10);
    let idx = TestValue::Index(3);
    let result = scal - idx;
    assert_eq!(result, scalar(7));
}

// ========== Scalar Multiplication of Groups (Edge Cases) ==========

#[test]
fn test_g1_scalar_mul_zero() {
    let g = random_g1();
    let zero = scalar(0);
    let result = zero * g;
    assert_eq!(result, TestValue::g1(G1Projective::zero()));
}

#[test]
fn test_g2_scalar_mul_zero() {
    let g = random_g2();
    let zero = scalar(0);
    let result = zero * g;
    assert_eq!(result, TestValue::G2(G2Projective::zero().into()));
}

#[test]
fn test_g1_scalar_mul_one() {
    let g = random_g1();
    let one = scalar(1);
    let result = one * g.clone();
    assert_eq!(result, g);
}

#[test]
fn test_g2_scalar_mul_one() {
    let g = random_g2();
    let one = scalar(1);
    let result = one * g.clone();
    assert_eq!(result, g);
}

#[test]
fn test_g1_scalar_mul_associativity() {
    // (a * b) * G = a * (b * G)
    let g = random_g1();
    let a = scalar(3);
    let b = scalar(5);
    let lhs = (a.clone() * b.clone()) * g.clone();
    let rhs = a * (b * g);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g2_scalar_mul_associativity() {
    // (a * b) * G = a * (b * G)
    let g = random_g2();
    let a = scalar(3);
    let b = scalar(5);
    let lhs = (a.clone() * b.clone()) * g.clone();
    let rhs = a * (b * g);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g1_index_mul() {
    // Index should coerce to scalar for group multiplication
    let g = random_g1();
    let idx = TestValue::Index(5);
    let scal = scalar(5);
    assert_eq!(idx * g.clone(), scal * g);
}

#[test]
fn test_g2_index_mul() {
    let g = random_g2();
    let idx = TestValue::Index(5);
    let scal = scalar(5);
    assert_eq!(idx * g.clone(), scal * g);
}

// ========== Vector Operations Edge Cases ==========

#[test]
fn test_vec_scalar_mul_zero() {
    let v = vec_scalar(&[1, 2, 3, 4]);
    let zero = scalar(0);
    let result = v * zero;
    assert_eq!(result, vec_scalar(&[0, 0, 0, 0]));
}

#[test]
fn test_vec_scalar_mul_one() {
    let v = vec_scalar(&[1, 2, 3, 4]);
    let one = scalar(1);
    let result = v.clone() * one;
    assert_eq!(result, v);
}

#[test]
fn test_empty_vec_operations() {
    // Empty vectors should work correctly
    let empty_idx: TestValue = TestValue::VecIndex(vec![].into());
    let empty_idx2: TestValue = TestValue::VecIndex(vec![].into());
    assert_eq!(
        empty_idx.clone() + empty_idx2.clone(),
        TestValue::VecIndex(vec![].into())
    );
    assert_eq!(
        empty_idx.clone() - empty_idx2.clone(),
        TestValue::VecIndex(vec![].into())
    );
    assert_eq!(
        empty_idx.clone() * empty_idx2.clone(),
        TestValue::VecIndex(vec![].into())
    );
}

#[test]
fn test_single_element_vec() {
    let a = TestValue::VecIndex(vec![5].into());
    let b = TestValue::VecIndex(vec![3].into());
    assert_eq!(a.clone() + b.clone(), TestValue::VecIndex(vec![8].into()));
    assert_eq!(a.clone() - b.clone(), TestValue::VecIndex(vec![2].into()));
    assert_eq!(a.clone() * b.clone(), TestValue::VecIndex(vec![15].into()));
}

// ========== Operations with Zero ==========

#[test]
fn test_scalar_add_zero() {
    let a = scalar(42);
    let zero = scalar(0);
    assert_eq!(a.clone() + zero.clone(), a.clone());
    assert_eq!(zero + a.clone(), a);
}

#[test]
fn test_scalar_sub_zero() {
    let a = scalar(42);
    let zero = scalar(0);
    assert_eq!(a.clone() - zero, a);
}

#[test]
fn test_zero_sub_scalar() {
    // 0 - a = -a
    let a = scalar(42);
    let zero = scalar(0);
    let neg_a = zero - a.clone();
    // Verify: a + (-a) = 0
    assert_eq!(a + neg_a, scalar(0));
}

#[test]
fn test_vec_scalar_add_zero() {
    let v = vec_scalar(&[1, 2, 3]);
    let zero = vec_scalar(&[0, 0, 0]);
    assert_eq!(v.clone() + zero.clone(), v);
}

// ========== G1/G2 Subtraction Tests ==========

#[test]
fn test_g1_sub_self() {
    let a = random_g1();
    assert_eq!(a.clone() - a, TestValue::g1(G1Projective::zero()));
}

#[test]
fn test_g2_sub_self() {
    let a = random_g2();
    assert_eq!(a.clone() - a, TestValue::G2(G2Projective::zero().into()));
}

#[test]
fn test_g1_sub_distributivity() {
    // a * (G1 - G2) = a * G1 - a * G2
    let g1 = random_g1();
    let g2 = random_g1();
    let a = random_scalar();
    let lhs = a.clone() * (g1.clone() - g2.clone());
    let rhs = (a.clone() * g1) - (a * g2);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_g2_sub_distributivity() {
    let g1 = random_g2();
    let g2 = random_g2();
    let a = random_scalar();
    let lhs = a.clone() * (g1.clone() - g2.clone());
    let rhs = (a.clone() * g1) - (a * g2);
    assert_eq!(lhs, rhs);
}

// ========== VecG1/VecG2 Operations ==========

#[test]
fn test_vec_g1_add() {
    let a = random_g1();
    let b = random_g1();
    let va = TestValue::vec_g1(vec![a.clone().into_g1(), b.clone().into_g1()]);
    let c = random_g1();
    let d = random_g1();
    let vb = TestValue::vec_g1(vec![c.clone().into_g1(), d.clone().into_g1()]);

    let result = va + vb;
    let expected = TestValue::vec_g1(vec![(a + c).into_g1(), (b + d).into_g1()]);
    assert_eq!(result, expected);
}

#[test]
fn test_vec_g2_add() {
    let a = random_g2();
    let b = random_g2();
    let va = TestValue::vec_g2(vec![a.clone().into_g2(), b.clone().into_g2()]);
    let c = random_g2();
    let d = random_g2();
    let vb = TestValue::vec_g2(vec![c.clone().into_g2(), d.clone().into_g2()]);

    let result = va + vb;
    let expected = TestValue::vec_g2(vec![(a + c).into_g2(), (b + d).into_g2()]);
    assert_eq!(result, expected);
}

#[test]
fn test_vec_g1_sub() {
    let a = random_g1();
    let b = random_g1();
    let va = TestValue::vec_g1(vec![a.clone().into_g1(), b.clone().into_g1()]);
    let vb = va.clone();

    let result = va - vb;
    let zero = G1Projective::zero();
    let expected = TestValue::vec_g1(vec![zero, zero]);
    assert_eq!(result, expected);
}

#[test]
fn test_vec_g2_sub() {
    let a = random_g2();
    let b = random_g2();
    let va = TestValue::vec_g2(vec![a.clone().into_g2(), b.clone().into_g2()]);
    let vb = va.clone();

    let result = va - vb;
    let zero = G2Projective::zero();
    let expected = TestValue::vec_g2(vec![zero, zero]);
    assert_eq!(result, expected);
}

// ========== Additional Distributivity Tests ==========

#[test]
fn test_vec_scalar_distributivity_with_index() {
    let v = vec_scalar(&[1, 2, 3]);
    let a = TestValue::Index(2);
    let b = TestValue::Index(3);
    // (a + b) * v = a * v + b * v
    let lhs = (a.clone() + b.clone()) * v.clone();
    let rhs = (a * v.clone()) + (b * v);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_index_distributivity() {
    let a = TestValue::Index(2);
    let b = TestValue::Index(3);
    let c = TestValue::Index(5);
    // a * (b + c) = a * b + a * c
    assert_eq!(
        a.clone() * (b.clone() + c.clone()),
        (a.clone() * b) + (a * c)
    );
}

#[test]
fn test_vec_index_distributivity() {
    let a = TestValue::VecIndex(vec![2, 3].into());
    let b = TestValue::VecIndex(vec![4, 5].into());
    let c = TestValue::VecIndex(vec![6, 7].into());
    // a * (b + c) = a * b + a * c
    assert_eq!(
        a.clone() * (b.clone() + c.clone()),
        (a.clone() * b) + (a * c)
    );
}

// ========== Field Axiom Completeness ==========

#[test]
fn test_field_division_left_identity() {
    // 1 / a * a = 1 (when a ≠ 0)
    let a = scalar(7);
    let one = scalar(1);
    let result = (one.clone() / a.clone()) * a;
    assert_eq!(result, one);
}

#[test]
fn test_field_division_right_identity() {
    // a / a = 1 (when a ≠ 0)
    let a = scalar(13);
    assert_eq!(a.clone() / a, scalar(1));
}

#[test]
fn test_field_division_distributivity() {
    // (a + b) / c = a / c + b / c
    let a = scalar(10);
    let b = scalar(5);
    let c = scalar(3);
    let lhs = (a.clone() + b.clone()) / c.clone();
    let rhs = (a / c.clone()) + (b / c);
    assert_eq!(lhs, rhs);
}

#[test]
fn test_scalar_div_associativity() {
    // a / (b / c) = (a * c) / b
    let a = scalar(24);
    let b = scalar(6);
    let c = scalar(2);
    let lhs = a.clone() / (b.clone() / c.clone());
    let rhs = (a * c) / b;
    assert_eq!(lhs, rhs);
}

// ========== Property-Based Tests for Polynomial Values ==========

use arbitrary::{Arbitrary, Unstructured};

/// Random univariate polynomial value (degree 1-4, non-zero coefficients)
#[derive(Debug, Clone)]
struct UniPoly(TestValue);

impl<'a> Arbitrary<'a> for UniPoly {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let degree: usize = u.int_in_range(1..=4)?;
        let mut coeffs = Vec::new();
        for _ in 0..=degree {
            coeffs.push(Fr::from(u.int_in_range(1u64..=100)?));
        }
        Ok(UniPoly(TestValue::poly(VirtualPolynomial::from_poly(
            PolyVariant::from_coeffs(coeffs),
        ))))
    }
}

/// Random MLE value with exactly 2 variables (4 evaluations)
#[derive(Debug, Clone)]
struct Mle2Poly(TestValue);

impl<'a> Arbitrary<'a> for Mle2Poly {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut evals = Vec::new();
        for _ in 0..4 {
            evals.push(Fr::from(u.int_in_range(1u64..=100)?));
        }
        Ok(Mle2Poly(TestValue::poly(VirtualPolynomial::from_poly(
            PolyVariant::DenseMle(DenseMle::new(2, evals)),
        ))))
    }
}

/// Non-zero scalar polynomial (for division tests)
#[derive(Debug, Clone)]
struct NonZeroScalarPoly(TestValue);

impl<'a> Arbitrary<'a> for NonZeroScalarPoly {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let s = Fr::from(u.int_in_range(1u64..=100)?);
        Ok(NonZeroScalarPoly(TestValue::poly(
            VirtualPolynomial::from_scalar(s),
        )))
    }
}

fn zero_poly() -> TestValue {
    TestValue::poly(VirtualPolynomial::from_scalar(Fr::from(0)))
}

fn one_poly() -> TestValue {
    TestValue::poly(VirtualPolynomial::from_scalar(Fr::from(1)))
}

// --- Cross-type interaction: VPoly + Uni → Poly ---

#[test]
fn pbt_vpoly_add_uni() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        let vpoly = a.0.clone() * b.0.clone();
        let c: UniPoly = u.arbitrary()?;
        let result = vpoly + c.0;
        assert!(matches!(result, TestValue::Poly(_)));
        Ok(())
    });
}

// --- Cross-type interaction: VPoly + Mle → Poly ---

#[test]
fn pbt_vpoly_add_mle() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        let vpoly = a.0.clone() * b.0.clone();
        let c: Mle2Poly = u.arbitrary()?;
        let result = vpoly + c.0;
        assert!(matches!(result, TestValue::Poly(_)));
        Ok(())
    });
}

// --- Cross-type interaction: Uni + Mle → Poly ---

#[test]
fn pbt_uni_add_mle() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        let result = a.0 + b.0;
        assert!(matches!(result, TestValue::Poly(_)));
        Ok(())
    });
}

// --- Univariate add: commutativity ---

#[test]
fn pbt_uni_add_commutativity() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: UniPoly = u.arbitrary()?;
        assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
        Ok(())
    });
}

// --- Univariate add: associativity ---

#[test]
fn pbt_uni_add_associativity() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: UniPoly = u.arbitrary()?;
        let c: UniPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
        Ok(())
    });
}

// --- Univariate add: identity (zero polynomial) ---

#[test]
fn pbt_uni_add_identity() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let z = zero_poly();
        assert_eq!(a.0.clone() + z.clone(), a.0.clone());
        assert_eq!(z + a.0.clone(), a.0);
        Ok(())
    });
}

// --- Univariate add/sub inverse: a + b - b = a ---

#[test]
fn pbt_uni_add_sub_inverse() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: UniPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
        Ok(())
    });
}

// --- Univariate mul: commutativity ---

#[test]
fn pbt_uni_mul_commutativity() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: UniPoly = u.arbitrary()?;
        assert_eq!(a.0.clone() * b.0.clone(), b.0 * a.0);
        Ok(())
    });
}

// --- Univariate mul: associativity ---

#[test]
fn pbt_uni_mul_associativity() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: UniPoly = u.arbitrary()?;
        let c: UniPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() * b.0.clone()) * c.0.clone(), a.0 * (b.0 * c.0));
        Ok(())
    });
}

// --- Univariate mul: identity (one polynomial) ---

#[test]
fn pbt_uni_mul_identity() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let o = one_poly();
        assert_eq!(a.0.clone() * o.clone(), a.0.clone());
        assert_eq!(o * a.0.clone(), a.0);
        Ok(())
    });
}

// --- Univariate mul/div inverse: (a * b) / b = a ---

#[test]
fn pbt_uni_mul_div_inverse() {
    arbtest::arbtest(|u| {
        let a: UniPoly = u.arbitrary()?;
        let b: NonZeroScalarPoly = u.arbitrary()?;
        let result = (a.0.clone() * b.0.clone()) / b.0;
        assert_eq!(result, a.0);
        Ok(())
    });
}

// --- MLE add: commutativity ---

#[test]
fn pbt_mle_add_commutativity() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
        Ok(())
    });
}

// --- MLE add: associativity ---

#[test]
fn pbt_mle_add_associativity() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        let c: Mle2Poly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
        Ok(())
    });
}

// --- MLE add: identity (zero polynomial) ---

#[test]
fn pbt_mle_add_identity() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let z = zero_poly();
        assert_eq!(a.0.clone() + z.clone(), a.0.clone());
        assert_eq!(z + a.0.clone(), a.0);
        Ok(())
    });
}

// --- MLE add/sub inverse: a + b - b = a ---

#[test]
fn pbt_mle_add_sub_inverse() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
        Ok(())
    });
}

// --- MLE scalar mul/div inverse: (a * s) / s = a ---

#[test]
fn pbt_mle_scalar_mul_div_inverse() {
    arbtest::arbtest(|u| {
        let a: Mle2Poly = u.arbitrary()?;
        let s = Fr::from(u.int_in_range(1u64..=100)?);
        let sv = TestValue::Scalar(s);
        let result = (a.0.clone() * sv.clone()) / sv;
        assert_eq!(result, a.0);
        Ok(())
    });
}

// ========== VPoly (product polynomial) Property-Based Tests ==========

/// Uni-based VPoly: product of two random univariates (degree 1-3 each)
/// Normalizes to DenseUni, so PartialEq is exact.
#[derive(Debug, Clone)]
struct UniVPoly(TestValue);

impl<'a> Arbitrary<'a> for UniVPoly {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let a: UniPoly = u.arbitrary()?;
        let b: UniPoly = u.arbitrary()?;
        Ok(UniVPoly(a.0 * b.0))
    }
}

/// MLE-based VPoly: product of two random 2-variable MLEs.
/// Cannot normalize (MLE multiplication unsupported at PolyVariant level),
/// uses canonical structural comparison via sorted products.
#[derive(Debug, Clone)]
struct MleVPoly(TestValue);

impl<'a> Arbitrary<'a> for MleVPoly {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let a: Mle2Poly = u.arbitrary()?;
        let b: Mle2Poly = u.arbitrary()?;
        Ok(MleVPoly(a.0 * b.0))
    }
}

// --- Uni VPoly add: commutativity ---

#[test]
fn pbt_uni_vpoly_add_commutativity() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let b: UniVPoly = u.arbitrary()?;
        assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
        Ok(())
    });
}

// --- Uni VPoly add: associativity ---

#[test]
fn pbt_uni_vpoly_add_associativity() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let b: UniVPoly = u.arbitrary()?;
        let c: UniVPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
        Ok(())
    });
}

// --- Uni VPoly add: identity (zero) ---

#[test]
fn pbt_uni_vpoly_add_identity() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let z = zero_poly();
        assert_eq!(a.0.clone() + z.clone(), a.0.clone());
        assert_eq!(z + a.0.clone(), a.0);
        Ok(())
    });
}

// --- Uni VPoly add/sub inverse: a + b - b = a ---

#[test]
fn pbt_uni_vpoly_add_sub_inverse() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let b: UniVPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
        Ok(())
    });
}

// --- Uni VPoly mul: commutativity ---

#[test]
fn pbt_uni_vpoly_mul_commutativity() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let b: UniVPoly = u.arbitrary()?;
        assert_eq!(a.0.clone() * b.0.clone(), b.0 * a.0);
        Ok(())
    });
}

// --- Uni VPoly mul: associativity ---

#[test]
fn pbt_uni_vpoly_mul_associativity() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let b: UniVPoly = u.arbitrary()?;
        let c: UniVPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() * b.0.clone()) * c.0.clone(), a.0 * (b.0 * c.0));
        Ok(())
    });
}

// --- Uni VPoly mul: identity (one) ---

#[test]
fn pbt_uni_vpoly_mul_identity() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let o = one_poly();
        assert_eq!(a.0.clone() * o.clone(), a.0.clone());
        assert_eq!(o * a.0.clone(), a.0);
        Ok(())
    });
}

// --- Uni VPoly scalar mul/div inverse: (a * s) / s = a ---

#[test]
fn pbt_uni_vpoly_scalar_mul_div_inverse() {
    arbtest::arbtest(|u| {
        let a: UniVPoly = u.arbitrary()?;
        let s: NonZeroScalarPoly = u.arbitrary()?;
        let result = (a.0.clone() * s.0.clone()) / s.0;
        assert_eq!(result, a.0);
        Ok(())
    });
}

// --- MLE VPoly add: commutativity ---

#[test]
fn pbt_mle_vpoly_add_commutativity() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let b: MleVPoly = u.arbitrary()?;
        assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
        Ok(())
    });
}

// --- MLE VPoly add: associativity ---

#[test]
fn pbt_mle_vpoly_add_associativity() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let b: MleVPoly = u.arbitrary()?;
        let c: MleVPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
        Ok(())
    });
}

// --- MLE VPoly add: identity (zero) ---

#[test]
fn pbt_mle_vpoly_add_identity() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let z = zero_poly();
        assert_eq!(a.0.clone() + z.clone(), a.0.clone());
        assert_eq!(z + a.0.clone(), a.0);
        Ok(())
    });
}

// --- MLE VPoly add/sub inverse: a + b - b = a ---

#[test]
fn pbt_mle_vpoly_add_sub_inverse() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let b: MleVPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
        Ok(())
    });
}

// --- MLE VPoly mul: commutativity ---

#[test]
fn pbt_mle_vpoly_mul_commutativity() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let b: MleVPoly = u.arbitrary()?;
        assert_eq!(a.0.clone() * b.0.clone(), b.0 * a.0);
        Ok(())
    });
}

// --- MLE VPoly mul: associativity ---

#[test]
fn pbt_mle_vpoly_mul_associativity() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let b: MleVPoly = u.arbitrary()?;
        let c: MleVPoly = u.arbitrary()?;
        assert_eq!((a.0.clone() * b.0.clone()) * c.0.clone(), a.0 * (b.0 * c.0));
        Ok(())
    });
}

// --- MLE VPoly mul: identity (one) ---

#[test]
fn pbt_mle_vpoly_mul_identity() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let o = one_poly();
        assert_eq!(a.0.clone() * o.clone(), a.0.clone());
        assert_eq!(o * a.0.clone(), a.0);
        Ok(())
    });
}

// --- MLE VPoly scalar mul/div inverse: (a * s) / s = a ---

#[test]
fn pbt_mle_vpoly_scalar_mul_div_inverse() {
    arbtest::arbtest(|u| {
        let a: MleVPoly = u.arbitrary()?;
        let s = Fr::from(u.int_in_range(1u64..=100)?);
        let sv = TestValue::Scalar(s);
        let result = (a.0.clone() * sv.clone()) / sv;
        assert_eq!(result, a.0);
        Ok(())
    });
}

#[test]
fn sparse_reduce_matches_generic() {
    // A single SparseMle factor forces the sparse fused path; the round poly
    // must match the trusted generic per-(t, tail) evaluate_mv oracle.
    let evals = vec![
        (0, Fr::from(2u64)),
        (3, Fr::from(5u64)),
        (5, Fr::from(7u64)),
    ];
    let vp = VirtualPolynomial::from_poly(PolyVariant::SparseMle { num_vars: 3, evals });
    for free_variable in 0..3 {
        let round = vp.sum_over_hypercube_except(free_variable, 2, 1);
        for t_u in [0u64, 1, 2, 3, 4] {
            let t = Fr::from(t_u);
            let mut expected = Fr::zero();
            for tail in 0..4usize {
                let b0 = if tail & 1 == 1 { Fr::one() } else { Fr::zero() };
                let b1 = if (tail >> 1) & 1 == 1 {
                    Fr::one()
                } else {
                    Fr::zero()
                };
                let mut point = vec![b0, b1];
                point.insert(free_variable, t);
                expected += vp.evaluate_mv(&point).unwrap();
            }
            assert_eq!(round.evaluate_uv(&t), expected, "round mismatch at t={t_u}");
        }
    }
}

// ========== Division by zero and operand order ==========

/// The univariate polynomial with these coefficients, lowest degree first.
fn uni(coeffs: &[u64]) -> TestValue {
    TestValue::poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
        DenseUni::new(coeffs.iter().map(|&c| Fr::from(c)).collect()),
    )))
}

fn vec_index(xs: &[usize]) -> TestValue {
    TestValue::VecIndex(xs.to_vec().into())
}

#[test]
fn test_division_keeps_operand_order() {
    assert_eq!(
        TestValue::Index(12) / vec_index(&[2, 3]),
        vec_index(&[6, 4])
    );
    assert_eq!(TestValue::Index(7) % vec_index(&[2, 3]), vec_index(&[1, 1]));
    assert_eq!(scalar(6) / TestValue::Index(2), scalar(3));
}

#[test]
fn test_vec_gt_div_scalar_divides_every_entry() {
    let v = TestValue::random(&mut thread_rng(), &ATyp::vec_gt(3));
    assert_eq!(v.clone() / scalar(1), v);
}

#[test]
fn test_division_by_zero_fails() {
    let div = |a: TestValue, b: TestValue| a.value_bin(BinOp::Div, b);
    let rem = |a: TestValue, b: TestValue| a.value_bin(BinOp::Rem, b);
    assert_eq!(
        div(TestValue::Index(1), TestValue::Index(0)),
        Err(DivisionByZero)
    );
    assert_eq!(
        div(TestValue::Index(1), vec_index(&[1, 0])),
        Err(DivisionByZero)
    );
    assert_eq!(
        div(vec_index(&[4, 6]), vec_index(&[2, 0])),
        Err(DivisionByZero)
    );
    assert_eq!(
        rem(TestValue::Index(1), TestValue::Index(0)),
        Err(DivisionByZero)
    );
    assert_eq!(
        rem(vec_index(&[4, 6]), TestValue::Index(0)),
        Err(DivisionByZero)
    );
    assert_eq!(div(scalar(1), TestValue::Index(0)), Err(DivisionByZero));
    assert_eq!(div(random_g1(), scalar(0)), Err(DivisionByZero));
    assert_eq!(div(random_g1(), vec_scalar(&[1, 0])), Err(DivisionByZero));
    assert_eq!(div(uni(&[1, 2]), scalar(0)), Err(DivisionByZero));
    assert_eq!(div(uni(&[1, 2]), uni(&[0])), Err(DivisionByZero));
    assert_eq!(div(scalar(1), uni(&[0])), Err(DivisionByZero));
}

#[test]
fn test_reduce_division_by_zero_fails() {
    // The first entry is the dividend, so it may be zero.
    assert!(vec_scalar(&[0, 2]).value_reduce(BinOp::Div).is_ok());
    assert_eq!(
        vec_scalar(&[6, 0]).value_reduce(BinOp::Div),
        Err(DivisionByZero)
    );
}

#[test]
fn test_interpolation_at_repeated_points_fails() {
    let evals = vec_scalar(&[1, 2]);
    assert_eq!(
        evals.value_interpolate(Some(&vec_scalar(&[3, 3]))),
        Err(DivisionByZero)
    );
    assert!(evals.value_interpolate(Some(&vec_scalar(&[3, 4]))).is_ok());
}
