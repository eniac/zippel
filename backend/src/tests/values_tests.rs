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
    let P = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let Q = Value::<TestConfig>::random(&mut rng, &ATyp::g1());
    let S = Value::<TestConfig>::random(&mut rng, &ATyp::g2());
    let pair1 = (P.clone() + Q.clone()).pair(S.clone());
    let pair2 = P.clone().pair(S.clone());
    let pair3 = Q.clone().pair(S.clone());
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
        assert_deq!(left, right);
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


