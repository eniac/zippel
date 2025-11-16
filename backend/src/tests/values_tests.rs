use crate::{Value, ATyp, ArkConfig, ABase};
use crate::config::ArkBls12_381;
use ark_bls12_381::Fr;
use ark_ff::Zero;
use ark_ec::{CurveGroup, PrimeGroup, AffineRepr};
use ark_std::test_rng;
use share::assert_deq;
use lang::typ::CRange;

type TestConfig = ArkBls12_381;

// Tests moved from values.rs
#[test]
fn test_add_comm() {
    // Scalar + Scalar
    let mut rng = test_rng();
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    assert_deq!(&a + &b, &b + &a);

    // Group1 + Group1
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    assert_deq!(&a + &b, &b + &a);

    // Group2 + Group2
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
    assert_deq!(&a + &b, &b + &a);

    // GT + GT
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::gt());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::gt());
    assert_deq!(&a + &b, &b + &a);

    // Vec<Scalar> + Vec<Scalar>
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    assert_deq!(&a + &b, &b + &a);

    // Vec<Index> + Vec<Index>
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    assert_deq!(&a + &b, &b + &a);

    // Vec<Scalar> + Vec<Index>
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::new(0, 10), 10));
    assert_deq!(&a + &b, &b + &a);
}

#[test]
fn test_mul_comm() {
    // Scalar * Scalar
    let mut rng = test_rng();
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    assert_deq!(&a * &b, &b * &a);

    // Vec<Scalar> * Vec<Scalar>
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::scalar()), 10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::scalar()), 10));
    assert_deq!(&a * &b, &b * &a);

    // Vec<Index> * Vec<Index>
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    assert_deq!(&a * &b, &b * &a);

    // Vec<Scalar> * Vec<Index>
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    assert_deq!(&a * &b, &b * &a);

    let mut a = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let mut b1 = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
    let b2 = b1.clone();
    Value::value_pair(&a, &mut b1);
    Value::value_pair(&b2, &mut a);
    assert_deq!(b1, a);
}

#[test]
fn coef_eval_test() {
    let mut rng = test_rng();
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(8));
    let c = a.value_fft().value_ifft();
    assert_deq!(&c, &a);

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(8));
    let c = a.value_ifft().value_fft();
    assert_deq!(&c, &a);
}

#[test]
fn pairing_test() {
    let mut rng = test_rng();
    let p = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let q = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let s = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
    let pair1 = (p.clone() + q.clone()).pair(s.clone());
    let pair2 = p.clone().pair(s.clone());
    let pair3 = q.clone().pair(s.clone());
    let pair4 = pair2 + pair3;
    assert_deq!(&pair1, &pair4);
}

#[test]
fn inverse_test() {
    let mut rng = test_rng();
    let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_g1(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_g2(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = &(&b.clone() / &b.clone()) * &a;
    assert_deq!(&a, &c);
    assert_deq!(&a * &(&b.clone() / &b.clone()), &(&b.clone() / &b.clone()) * &a);
    assert_deq!((&a * &b.clone()) / b.clone(), a);

    let a = Value::<TestConfig>::random(&mut rng, &&ATyp::vec_g1(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = &(&b.clone() / &b.clone()) * &a;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::random(&mut rng, &&ATyp::vec_g2(10));
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = &(&b.clone() / &b.clone()) * &a;
    assert_deq!(&a, &c);

    let a = Value::<TestConfig>::scalar_from_usize(1);
    let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = (&a/&b).dot(b.clone());
    assert_deq!(&c, &Value::<TestConfig>::scalar_from_usize(10));

    let a = Value::<TestConfig>::random(&mut rng, &ATyp::Uni(2));
    let b= a.clone() * a.clone();
    let c = b.clone() / a.clone();
    assert_deq!(&a, &c);
}

// Existing tests below

    #[test]
    fn test_scalar_from_usize() {
        let val = Value::<TestConfig>::scalar_from_usize(42);
        match val {
            Value::Scalar(f) => assert_eq!(f, Fr::from(42u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_zero_scalar() {
        let val = Value::<TestConfig>::zero(&ATyp::scalar());
        match val {
            Value::Scalar(f) => assert!(f.is_zero()),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_zero_g1() {
        let val = Value::<TestConfig>::zero(&ATyp::g1());
        match val {
            Value::G1(g) => assert!(g.into_affine().is_zero()),
            _ => panic!("Expected G1"),
        }
    }

    #[test]
    fn test_zero_vec() {
        let val = Value::<TestConfig>::zero(&ATyp::vec_scalar(5));
        match &val {
            Value::VecScalar(v) => {
                assert_eq!(v.len(), 5);
                for f in v {
                    assert!(f.is_zero());
                }
            }
            _ => panic!("Expected VecScalar"),
        }
    }

    #[test]
    fn test_is_one_true() {
        let val = Value::<TestConfig>::Scalar(Fr::from(1u32));
        assert!(val.is_one());
    }

    #[test]
    fn test_is_one_false() {
        let val = Value::<TestConfig>::Scalar(Fr::from(2u32));
        assert!(!val.is_one());
    }

    #[test]
    fn test_is_zero_true() {
        let val = Value::<TestConfig>::Scalar(Fr::zero());
        assert!(val.is_zero());
    }

    #[test]
    fn test_is_zero_false() {
        let val = Value::<TestConfig>::Scalar(Fr::from(1u32));
        assert!(!val.is_zero());
    }

    #[test]
    fn test_value_vec_construction() {
        let vec = vec![
            Value::<TestConfig>::Scalar(Fr::from(1u32)),
            Value::<TestConfig>::Scalar(Fr::from(2u32)),
            Value::<TestConfig>::Scalar(Fr::from(3u32)),
        ];
        let val = Value::value_vec(vec);
        match &val {
            Value::VecScalar(v) => assert_eq!(v.len(), 3),
            _ => panic!("Expected VecScalar"),
        }
    }

    #[test]
    fn test_is_vec_true() {
        let val = Value::<TestConfig>::Vec(vec![]);
        assert!(val.is_vec());
    }

    #[test]
    fn test_is_vec_false() {
        let val = Value::<TestConfig>::Scalar(Fr::zero());
        assert!(!val.is_vec());
    }

    #[test]
    fn test_add_scalars() {
        let a = Value::<TestConfig>::Scalar(Fr::from(10u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(20u32));
        let result = a + b;
        match result {
            Value::Scalar(f) => assert_eq!(f, Fr::from(30u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_sub_scalars() {
        let a = Value::<TestConfig>::Scalar(Fr::from(50u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(20u32));
        let result = a - b;
        match result {
            Value::Scalar(f) => assert_eq!(f, Fr::from(30u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_mul_scalars() {
        let a = Value::<TestConfig>::Scalar(Fr::from(6u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(7u32));
        let result = a * b;
        match result {
            Value::Scalar(f) => assert_eq!(f, Fr::from(42u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_div_scalars() {
        let a = Value::<TestConfig>::Scalar(Fr::from(42u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(6u32));
        let result = a / b;
        match result {
            Value::Scalar(f) => assert_eq!(f, Fr::from(7u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_not_bool() {
        let val = Value::<TestConfig>::Bool(true);
        let result = val.not();
        match result {
            Value::Bool(b) => assert!(!b),
            _ => panic!("Expected Bool"),
        }
    }

    #[test]
    fn test_equ_scalars_equal() {
        let a = Value::<TestConfig>::Scalar(Fr::from(42u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(42u32));
        assert!(Value::equ(&a, &b));
    }

    #[test]
    fn test_equ_scalars_not_equal() {
        let a = Value::<TestConfig>::Scalar(Fr::from(42u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(43u32));
        assert!(!Value::equ(&a, &b));
    }

    #[test]
    fn test_value_equ_returns_bool() {
        let a = Value::<TestConfig>::Scalar(Fr::from(42u32));
        let b = Value::<TestConfig>::Scalar(Fr::from(42u32));
        let result = a.value_equ(&b);
        match result {
            Value::Bool(true) => {},
            _ => panic!("Expected Bool(true)"),
        }
    }

    #[test]
    fn test_into_scalar() {
        let val = Value::<TestConfig>::Scalar(Fr::from(42u32));
        let f = val.into_scalar();
        assert_eq!(f, Fr::from(42u32));
    }

    #[test]
    fn test_into_index() {
        let val = Value::<TestConfig>::Index(7);
        let idx = val.into_index();
        assert_eq!(idx, 7);
    }

    #[test]
    fn test_typ_scalar() {
        let val = Value::<TestConfig>::Scalar(Fr::zero());
        assert_eq!(val.typ(), ATyp::scalar());
    }

    #[test]
    fn test_typ_g1() {
        let val = Value::<TestConfig>::G1(<TestConfig as ArkConfig>::G1::generator());
        assert_eq!(val.typ(), ATyp::g1());
    }

    #[test]
    fn test_typ_g2() {
        let val = Value::<TestConfig>::G2(<TestConfig as ArkConfig>::G2::generator());
        assert_eq!(val.typ(), ATyp::g2());
    }

    #[test]
    fn test_typ_bool() {
        let val = Value::<TestConfig>::Bool(true);
        assert_eq!(val.typ(), ATyp::bool());
    }

    #[test]
    fn test_typ_index() {
        let val = Value::<TestConfig>::Index(0);
        // Index types have a Fin range, just verify it's a Fin type
        match val.typ() {
            ATyp::Base(ABase::Fin(_)) => {},
            _ => panic!("Expected Fin type for Index"),
        }
    }

    #[test]
    fn test_add_assign() {
        let mut val = Value::<TestConfig>::Scalar(Fr::from(10u32));
        val += Value::<TestConfig>::Scalar(Fr::from(5u32));
        match val {
            Value::Scalar(f) => assert_eq!(f, Fr::from(15u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_mul_assign() {
        let mut val = Value::<TestConfig>::Scalar(Fr::from(10u32));
        val *= Value::<TestConfig>::Scalar(Fr::from(5u32));
        match val {
            Value::Scalar(f) => assert_eq!(f, Fr::from(50u32)),
            _ => panic!("Expected Scalar"),
        }
    }

    #[test]
    fn test_add_vectors() {
        let v1 = Value::<TestConfig>::VecScalar(vec![
            Fr::from(1u32),
            Fr::from(2u32),
        ]);
        let v2 = Value::<TestConfig>::VecScalar(vec![
            Fr::from(10u32),
            Fr::from(20u32),
        ]);
        let result = v1 + v2;
        match &result {
            Value::VecScalar(v) => {
                assert_eq!(v.len(), 2);
                assert_eq!(v[0], Fr::from(11u32));
                assert_eq!(v[1], Fr::from(22u32));
            }
            _ => panic!("Expected VecScalar"),
        }
    }

    #[test]
    fn test_value_concat() {
        let v1 = Value::<TestConfig>::VecScalar(vec![Fr::from(1u32)]);
        let v2 = Value::<TestConfig>::VecScalar(vec![Fr::from(2u32)]);
        let result = v1.value_concat(v2);
        match &result {
            Value::VecScalar(v) => {
                assert_eq!(v.len(), 2);
            }
            _ => panic!("Expected VecScalar"),
        }
    }

    #[test]
    fn test_discriminant_order() {
        // Just verify it returns something consistent
        let scalar = Value::<TestConfig>::Scalar(Fr::zero());
        let g1 = Value::<TestConfig>::G1(<TestConfig as ArkConfig>::G1::generator());
        let vec = Value::<TestConfig>::Vec(vec![]);
        
        assert!(scalar.discriminant_order() < 20);
        assert!(g1.discriminant_order() < 20);
        assert!(vec.discriminant_order() < 20);
    }

    // New comprehensive algebraic property tests
    #[test]
    fn test_scalar_associativity_addition() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        
        let left = (a.clone() + b.clone()) + c.clone();
        let right = a + (b + c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_scalar_associativity_multiplication() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        
        let left = (a.clone() * b.clone()) * c.clone();
        let right = a * (b * c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_scalar_distributivity() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        
        let left = a.clone() * (b.clone() + c.clone());
        let right = (a.clone() * b) + (a * c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_scalar_additive_identity() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let zero = Value::<TestConfig>::zero(&ATyp::scalar());
        
        assert_deq!(a.clone() + zero, a);
    }

    #[test]
    fn test_scalar_multiplicative_identity() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let one = Value::<TestConfig>::Scalar(Fr::from(1u32));
        
        assert_deq!(a.clone() * one, a);
    }

    #[test]
    fn test_scalar_additive_inverse() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let zero = Value::<TestConfig>::zero(&ATyp::scalar());
        
        let result = a.clone() - a;
        assert_deq!(result, zero);
    }

    #[test]
    fn test_g1_associativity_addition() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        
        let left = (a.clone() + b.clone()) + c.clone();
        let right = a + (b + c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_g1_additive_identity() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        let zero = Value::<TestConfig>::zero(&ATyp::g1());
        
        assert_deq!(a.clone() + zero, a);
    }

    #[test]
    fn test_g1_scalar_distributivity() {
        let mut rng = test_rng();
        let g = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::scalar());
        
        let left = g.clone() * (a.clone() + b.clone());
        let right = (g.clone() * a) + (g * b);
        
        // Subtract to check if difference is zero (mathematical equality)
        let diff = left.clone() - right.clone();
        assert!(diff.is_zero(), "G1 scalar distributivity failed: left - right = {:?}", diff);
    }

    #[test]
    fn test_g2_associativity_addition() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
        
        let left = (a.clone() + b.clone()) + c.clone();
        let right = a + (b + c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_g2_additive_identity() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
        let zero = Value::<TestConfig>::zero(&ATyp::g2());
        
        assert_deq!(a.clone() + zero, a);
    }

    #[test]
    fn test_vec_scalar_associativity_addition() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        
        let left = (a.clone() + b.clone()) + c.clone();
        let right = a + (b + c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_vec_scalar_distributivity() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        let c = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        
        let left = a.clone() * (b.clone() + c.clone());
        let right = (a.clone() * b) + (a * c);
        assert_deq!(left, right);
    }

    #[test]
    fn test_index_commutativity() {
        let a = Value::<TestConfig>::Index(5);
        let b = Value::<TestConfig>::Index(7);
        assert_deq!(a.clone() + b.clone(), b.clone() + a.clone());
        assert_deq!(a.clone() * b.clone(), b * a);
    }

    #[test]
    fn test_bool_operations() {
        let t = Value::<TestConfig>::Bool(true);
        let f = Value::<TestConfig>::Bool(false);
        
        assert_deq!(t.clone() & t.clone(), Value::<TestConfig>::Bool(true));
        assert_deq!(t.clone() & f.clone(), Value::<TestConfig>::Bool(false));
        assert_deq!(f.clone() & f.clone(), Value::<TestConfig>::Bool(false));
        
        assert_deq!(t.clone() | t.clone(), Value::<TestConfig>::Bool(true));
        assert_deq!(t.clone() | f.clone(), Value::<TestConfig>::Bool(true));
        assert_deq!(f.clone() | f, Value::<TestConfig>::Bool(false));
    }

    #[test]
    fn test_poly_operations() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(4));
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(4));
        
        let p1 = a.value_poly();
        let p2 = b.value_poly();
        
        let sum = p1 + p2;
        match sum {
            Value::Poly(_) => {},
            _ => panic!("Expected Poly"),
        }
    }

    #[test]
    fn test_mle_operations() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(8));
        
        let mle = a.value_mle();
        match mle {
            Value::Mle(m) => assert_eq!(m.num_vars, 3),
            _ => panic!("Expected Mle"),
        }
    }

    // New comprehensive tests for uncovered operations

    #[test]
    fn test_division_operations() {
        let a = Value::<TestConfig>::scalar_from_usize(10);
        let b = Value::<TestConfig>::scalar_from_usize(2);
        let c = &a / &b;
        let expected = Value::<TestConfig>::scalar_from_usize(5);
        assert_deq!(&c, &expected);

        // Division by one
        let one = Value::<TestConfig>::scalar_from_usize(1);
        let result = &a / &one;
        assert_deq!(&result, &a);
    }

    #[test]
    fn test_remainder_operations() {
        // value_rem computes self % other and stores in other
        let a = Value::<TestConfig>::Index(10);
        let mut b = Value::<TestConfig>::Index(3);
        a.value_rem(&mut b);
        assert_deq!(&b, &Value::<TestConfig>::Index(1));
        
        // Using % operator with references
        let a = Value::<TestConfig>::Index(10);
        let b = Value::<TestConfig>::Index(3);
        let c = &a % &b;
        assert_deq!(&c, &Value::<TestConfig>::Index(1));
    }


    #[test]
    fn test_bitxor_as_pow() {
        // In this DSL, ^ operator is used for exponentiation, not XOR
        let base = Value::<TestConfig>::scalar_from_usize(2);
        let exp = Value::<TestConfig>::Index(3);
        let result = &base ^ &exp;
        assert_deq!(&result, &Value::<TestConfig>::scalar_from_usize(8));
        
        // Test with Index ^ Index
        let base = Value::<TestConfig>::Index(3);
        let exp = Value::<TestConfig>::Index(2);
        let result = &base ^ &exp;
        assert_deq!(&result, &Value::<TestConfig>::Index(9));
    }

    #[test]
    fn test_not_operation() {
        let t = Value::<TestConfig>::Bool(true);
        let f = Value::<TestConfig>::Bool(false);
        
        assert_deq!(t.not(), Value::<TestConfig>::Bool(false));
        assert_deq!(f.not(), Value::<TestConfig>::Bool(true));
    }

    #[test]
    fn test_value_pow() {
        // value_pow(a, b) computes a^b and stores result in b
        let base = Value::<TestConfig>::scalar_from_usize(2);
        let mut exp = Value::<TestConfig>::Index(3);
        base.value_pow(&mut exp);
        // Result is 2^3 = 8, stored in exp
        assert_deq!(&exp, &Value::<TestConfig>::scalar_from_usize(8));
    }

    #[test]
    fn test_value_dot() {
        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        let mut b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        // value_dot(a, b) computes dot product and stores in b
        a.value_dot(&mut b);
        match b {
            Value::Scalar(_) => {},
            _ => panic!("Expected Scalar result from dot product"),
        }
    }


    #[test]
    fn test_value_concat_extended() {
        let a = Value::<TestConfig>::VecScalar(vec![Fr::from(1u64), Fr::from(2u64)]);
        let b = Value::<TestConfig>::VecScalar(vec![Fr::from(3u64), Fr::from(4u64)]);
        let c = a.value_concat(b);
        match c {
            Value::VecScalar(v) => assert_eq!(v.len(), 4),
            _ => panic!("Expected VecScalar"),
        }

        let a = Value::<TestConfig>::VecIndex(vec![1, 2]);
        let b = Value::<TestConfig>::VecIndex(vec![3, 4]);
        let c = a.value_concat(b);
        match c {
            Value::VecIndex(v) => assert_eq!(v.len(), 4),
            _ => panic!("Expected VecIndex"),
        }
    }

    #[test]
    fn test_elliptic_curve_pairing() {
        // value_pair and pair() perform pairing operations G1 x G2 -> GT
        let g1 = Value::<TestConfig>::G1(<TestConfig as ArkConfig>::G1::generator());
        let g2 = Value::<TestConfig>::G2(<TestConfig as ArkConfig>::G2::generator());
        
        let gt_result = g1.pair(g2);
        match gt_result {
            Value::GT(_) => {},
            _ => panic!("Expected GT result from pairing"),
        }
    }


    #[test]
    fn test_value_equ() {
        let a = Value::<TestConfig>::scalar_from_usize(5);
        let b = Value::<TestConfig>::scalar_from_usize(5);
        let c = Value::<TestConfig>::scalar_from_usize(3);
        
        assert_deq!(a.value_equ(&b), Value::<TestConfig>::Bool(true));
        assert_deq!(a.value_equ(&c), Value::<TestConfig>::Bool(false));
    }

    #[test]
    fn test_equ_static() {
        let a = Value::<TestConfig>::scalar_from_usize(5);
        let b = Value::<TestConfig>::scalar_from_usize(5);
        let c = Value::<TestConfig>::scalar_from_usize(3);
        
        assert!(Value::<TestConfig>::equ(&a, &b));
        assert!(!Value::<TestConfig>::equ(&a, &c));
    }

    #[test]
    fn test_is_one() {
        let one = Value::<TestConfig>::scalar_from_usize(1);
        let two = Value::<TestConfig>::scalar_from_usize(2);
        
        assert!(one.is_one());
        assert!(!two.is_one());

        let one_idx = Value::<TestConfig>::Index(1);
        assert!(one_idx.is_one());
    }

    #[test]
    fn test_zero_creation() {
        let scalar_zero = Value::<TestConfig>::zero(&ATyp::scalar());
        match scalar_zero {
            Value::Scalar(s) => assert!(s.is_zero()),
            _ => panic!("Expected Scalar"),
        }

        let g1_zero = Value::<TestConfig>::zero(&ATyp::g1());
        match g1_zero {
            Value::G1(_) => {},
            _ => panic!("Expected G1"),
        }

        let bool_zero = Value::<TestConfig>::zero(&ATyp::bool());
        assert_deq!(bool_zero, Value::<TestConfig>::Bool(false));

        let index_zero = Value::<TestConfig>::zero(&ATyp::fin(CRange::new(0, 10)));
        assert_deq!(index_zero, Value::<TestConfig>::Index(0));
    }

    #[test]
    fn test_discriminant_order_extended() {
        let bool_val = Value::<TestConfig>::Bool(true);
        let idx_val = Value::<TestConfig>::Index(5);
        let scalar_val = Value::<TestConfig>::scalar_from_usize(10);
        
        // Just ensure they return different values and don't panic
        let _d1 = bool_val.discriminant_order();
        let _d2 = idx_val.discriminant_order();
        let _d3 = scalar_val.discriminant_order();
    }

    #[test]
    fn test_typ_method() {
        let scalar = Value::<TestConfig>::scalar_from_usize(5);
        let typ = scalar.typ();
        assert!(typ.is_scalar());

        let idx = Value::<TestConfig>::Index(5);
        let _typ = idx.typ();

        let bool_val = Value::<TestConfig>::Bool(true);
        let typ = bool_val.typ();
        assert!(typ.is_bool());
    }

    #[test]
    fn test_serialize_value() {
        use crate::values::value_to_bytes;
        
        let scalar = Value::<TestConfig>::scalar_from_usize(42);
        let bytes = value_to_bytes(&scalar);
        assert!(bytes.is_ok());

        let bool_val = Value::<TestConfig>::Bool(true);
        let bytes = value_to_bytes(&bool_val);
        assert!(bytes.is_ok());

        let idx = Value::<TestConfig>::Index(10);
        let bytes = value_to_bytes(&idx);
        assert!(bytes.is_ok());
    }

    #[test]
    fn test_value_eval() {
        // Create a polynomial from coefficients [1, 2, 3]
        // This represents 1 + 2x + 3x^2
        let coeffs_vec = vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)];
        let poly = Value::<TestConfig>::Poly(ark_poly::DenseUVPolynomial::from_coefficients_vec(coeffs_vec));
        
        // Evaluate at points [0, 1, 2]
        let points = Value::<TestConfig>::VecScalar(vec![Fr::from(0u64), Fr::from(1u64), Fr::from(2u64)]);
        let result = poly.value_eval(points);
        match result {
            Value::VecScalar(v) => {
                // At x=0: 1
                // At x=1: 1 + 2 + 3 = 6
                // At x=2: 1 + 4 + 12 = 17
                assert_eq!(v[0], Fr::from(1u64));
                assert_eq!(v[1], Fr::from(6u64));
                assert_eq!(v[2], Fr::from(17u64));
            },
            _ => panic!("Expected VecScalar"),
        }
    }

    #[test]
    fn test_ram_operation() {
        let arr = Value::<TestConfig>::VecScalar(vec![
            Fr::from(10u64),
            Fr::from(20u64),
            Fr::from(30u64),
        ]);
        let idx = Value::<TestConfig>::Index(1);
        let result = arr.ram(idx);
        assert_deq!(result, Value::<TestConfig>::Scalar(Fr::from(20u64)));
    }

    #[test]
    fn test_vec_operations() {
        let mut rng = test_rng();
        
        // Vec<G1> operations
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_g1(5));
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_g1(5));
        let _c = &a + &b;

        // Vec<G2> operations
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_g2(5));
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_g2(5));
        let _c = &a + &b;

        // Vec<GT> operations
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::vec_gt(5));
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::vec_gt(5));
        let _c = &a + &b;
    }

    #[test]
    fn test_scalar_multiplication_variants() {
        let scalar = Value::<TestConfig>::scalar_from_usize(5);
        
        // Scalar * G1
        let g1 = Value::<TestConfig>::G1(<TestConfig as ArkConfig>::G1::generator());
        let _result = &scalar * &g1;
        let _result = &g1 * &scalar;

        // Scalar * G2
        let g2 = Value::<TestConfig>::G2(<TestConfig as ArkConfig>::G2::generator());
        let _result = &scalar * &g2;
        let _result = &g2 * &scalar;

        // Scalar * G1Affine
        let g1_affine = Value::<TestConfig>::G1Affine(<TestConfig as ArkConfig>::G1Affine::generator());
        let _result = &scalar * &g1_affine;

        // Scalar * G2Affine
        let g2_affine = Value::<TestConfig>::G2Affine(<TestConfig as ArkConfig>::G2Affine::generator());
        let _result = &scalar * &g2_affine;
    }

    #[test]
    fn test_vec_scalar_operations() {
        let mut rng = test_rng();
        
        // VecScalar * Scalar
        let vec_scalar = Value::<TestConfig>::random(&mut rng, &ATyp::vec_scalar(5));
        let scalar = Value::<TestConfig>::scalar_from_usize(3);
        let _result = &vec_scalar * &scalar;

        // VecIndex * Index
        let vec_idx = Value::<TestConfig>::random(&mut rng, &ATyp::vec_fin(CRange::new(0, 10), 5));
        let idx = Value::<TestConfig>::Index(2);
        let _result = &vec_idx * &idx;
    }

    #[test]
    fn test_mutable_operations() {
        let mut a = Value::<TestConfig>::scalar_from_usize(5);
        let b = Value::<TestConfig>::scalar_from_usize(3);
        
        a += b.clone();
        assert_deq!(&a, &Value::<TestConfig>::scalar_from_usize(8));

        let mut a = Value::<TestConfig>::scalar_from_usize(2);
        a *= b;
        assert_deq!(&a, &Value::<TestConfig>::scalar_from_usize(6));
    }

    #[test]
    fn test_sub_operations() {
        let a = Value::<TestConfig>::scalar_from_usize(10);
        let b = Value::<TestConfig>::scalar_from_usize(3);
        let c = &a - &b;
        assert_deq!(&c, &Value::<TestConfig>::scalar_from_usize(7));

        let mut rng = test_rng();
        let a = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        let b = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
        let _c = &a - &b;
    }


