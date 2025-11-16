#[cfg(test)]
mod value_tests {
    use crate::{Value, ATyp, ArkConfig, ABase};
    use crate::config::ArkBls12_381;
    use ark_bls12_381::Fr;
    use ark_ff::Zero;
    use ark_ec::{CurveGroup, PrimeGroup, AffineRepr};

    type TestConfig = ArkBls12_381;

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
}
