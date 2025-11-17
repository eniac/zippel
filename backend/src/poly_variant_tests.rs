#[cfg(test)]
mod tests {
    use super::super::poly_variant::*;
    use ark_ff::Field;
    use ark_poly::{
        univariate::{DensePolynomial, SparsePolynomial},
        DenseMultilinearExtension, MultilinearExtension,
        evaluations::multivariate::multilinear::SparseMultilinearExtension,
        DenseUVPolynomial,
    };
    use ark_bls12_381::Fr;

    // ========== Test Helpers ==========

    fn assert_poly_eq<F: Field>(a: &PolyVariant<F>, b: &PolyVariant<F>, msg: &str) {
        // Convert both to dense for comparison
        let a_dense = a.to_dense();
        let b_dense = b.to_dense();
        
        match (&a_dense, &b_dense) {
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                assert_eq!(p1, p2, "{}", msg);
            }
            (PolyVariant::DenseMle(m1), PolyVariant::DenseMle(m2)) => {
                assert_eq!(m1.num_vars, m2.num_vars, "{}: num_vars mismatch", msg);
                assert_eq!(m1.to_evaluations(), m2.to_evaluations(), "{}", msg);
            }
            _ => panic!("{}: incompatible polynomial types", msg),
        }
    }

    fn create_dense_uni_linear() -> PolyVariant<Fr> {
        // p(x) = 2x + 3
        let coeffs = vec![Fr::from(3u64), Fr::from(2u64)];
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs))
    }

    fn create_sparse_uni_linear() -> PolyVariant<Fr> {
        // p(x) = 2x + 3
        let coeffs = vec![(0, Fr::from(3u64)), (1, Fr::from(2u64))];
        PolyVariant::SparseUni(SparsePolynomial::from_coefficients_vec(coeffs))
    }

    fn create_dense_uni_quadratic() -> PolyVariant<Fr> {
        // p(x) = x^2 + 4x + 5
        let coeffs = vec![Fr::from(5u64), Fr::from(4u64), Fr::from(1u64)];
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs))
    }

    fn create_dense_mle_simple() -> PolyVariant<Fr> {
        // 2-var MLE with evals [1, 2, 3, 4]
        let evals = vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64), Fr::from(4u64)];
        PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(2, evals))
    }

    fn create_sparse_mle_simple() -> PolyVariant<Fr> {
        // 2-var sparse MLE with evals [1, 2, 3, 4]
        let evals = vec![
            (0, Fr::from(1u64)),
            (1, Fr::from(2u64)),
            (2, Fr::from(3u64)),
            (3, Fr::from(4u64)),
        ];
        PolyVariant::SparseMle(SparseMultilinearExtension::from_evaluations(2, &evals))
    }

    fn create_zero_uni() -> PolyVariant<Fr> {
        PolyVariant::from_scalar(Fr::from(0u64))
    }

    fn create_one_uni() -> PolyVariant<Fr> {
        PolyVariant::from_scalar(Fr::from(1u64))
    }

    fn create_scalar(val: u64) -> PolyVariant<Fr> {
        PolyVariant::from_scalar(Fr::from(val))
    }

    // ========== Ring Axiom Tests: Dense Univariate ==========

    #[test]
    fn test_dense_uni_addition_associativity() {
        let a = create_dense_uni_linear();
        let b = create_dense_uni_quadratic();
        let c = create_scalar(7);

        let left = a.clone().poly_add(&b.clone().poly_add(&c).unwrap()).unwrap();
        let right = a.poly_add(&b).unwrap().poly_add(&c).unwrap();

        assert_poly_eq(&left, &right, "DenseUni: (a+b)+c = a+(b+c)");
    }

    #[test]
    fn test_dense_uni_addition_commutativity() {
        let a = create_dense_uni_linear();
        let b = create_dense_uni_quadratic();

        let left = a.clone().poly_add(&b).unwrap();
        let right = b.poly_add(&a).unwrap();

        assert_poly_eq(&left, &right, "DenseUni: a+b = b+a");
    }

    #[test]
    fn test_dense_uni_addition_identity() {
        let a = create_dense_uni_linear();
        let zero = create_zero_uni();

        let result = a.clone().poly_add(&zero).unwrap();

        assert_poly_eq(&result, &a, "DenseUni: a+0 = a");
    }

    #[test]
    fn test_dense_uni_addition_inverse() {
        let a = create_dense_uni_linear();
        let zero = create_zero_uni();

        let neg_a = a.clone().poly_neg();
        let result = a.poly_add(&neg_a).unwrap();

        assert_poly_eq(&result, &zero, "DenseUni: a+(-a) = 0");
    }

    #[test]
    fn test_dense_uni_multiplication_associativity() {
        let a = create_dense_uni_linear();
        let b = create_dense_uni_quadratic();
        let c = create_scalar(5);

        let left = a.clone().poly_mul(&b.clone().poly_mul(&c).unwrap()).unwrap();
        let right = a.poly_mul(&b).unwrap().poly_mul(&c).unwrap();

        assert_poly_eq(&left, &right, "DenseUni: (a*b)*c = a*(b*c)");
    }

    #[test]
    fn test_dense_uni_multiplication_identity() {
        let a = create_dense_uni_linear();
        let one = create_one_uni();

        let result = a.clone().poly_mul(&one).unwrap();

        assert_poly_eq(&result, &a, "DenseUni: a*1 = a");
    }

    #[test]
    fn test_dense_uni_left_distributivity() {
        let a = create_dense_uni_linear();
        let b = create_dense_uni_quadratic();
        let c = create_scalar(3);

        let left = a.clone().poly_mul(&b.clone().poly_add(&c).unwrap()).unwrap();
        let right = a.clone().poly_mul(&b).unwrap().poly_add(&a.poly_mul(&c).unwrap()).unwrap();

        assert_poly_eq(&left, &right, "DenseUni: a*(b+c) = a*b + a*c");
    }

    #[test]
    fn test_dense_uni_right_distributivity() {
        let a = create_dense_uni_linear();
        let b = create_dense_uni_quadratic();
        let c = create_scalar(3);

        let left = a.clone().poly_add(&b).unwrap().poly_mul(&c.clone()).unwrap();
        let right = a.poly_mul(&c.clone()).unwrap().poly_add(&b.poly_mul(&c).unwrap()).unwrap();

        assert_poly_eq(&left, &right, "DenseUni: (a+b)*c = a*c + b*c");
    }

    #[test]
    fn test_dense_uni_subtraction_as_inverse() {
        let a = create_dense_uni_linear();
        let b = create_dense_uni_quadratic();

        let sub_result = a.clone().poly_sub(&b).unwrap();
        let add_neg_result = a.poly_add(&b.poly_neg()).unwrap();

        assert_poly_eq(&sub_result, &add_neg_result, "DenseUni: a-b = a+(-b)");
    }

    // ========== Ring Axiom Tests: Sparse Univariate ==========

    #[test]
    fn test_sparse_uni_addition_associativity() {
        let a = create_sparse_uni_linear();
        let b = create_dense_uni_quadratic(); // Mix sparse and dense
        let c = create_scalar(7);

        let left = a.clone().poly_add(&b.clone().poly_add(&c).unwrap()).unwrap();
        let right = a.poly_add(&b).unwrap().poly_add(&c).unwrap();

        assert_poly_eq(&left, &right, "SparseUni: (a+b)+c = a+(b+c)");
    }

    #[test]
    fn test_sparse_uni_addition_commutativity() {
        let a = create_sparse_uni_linear();
        let b = create_dense_uni_quadratic();

        let left = a.clone().poly_add(&b).unwrap();
        let right = b.poly_add(&a).unwrap();

        assert_poly_eq(&left, &right, "SparseUni: a+b = b+a");
    }

    #[test]
    fn test_sparse_uni_multiplication_associativity() {
        let a = create_sparse_uni_linear();
        let b = create_dense_uni_quadratic();
        let c = create_scalar(5);

        let left = a.clone().poly_mul(&b.clone().poly_mul(&c).unwrap()).unwrap();
        let right = a.poly_mul(&b).unwrap().poly_mul(&c).unwrap();

        assert_poly_eq(&left, &right, "SparseUni: (a*b)*c = a*(b*c)");
    }

    // ========== Ring Axiom Tests: Dense MLE ==========

    #[test]
    fn test_dense_mle_addition_associativity() {
        let a = create_dense_mle_simple();
        let b = create_dense_mle_simple();
        let c = create_dense_mle_simple();

        let left = a.clone().poly_add(&b.clone().poly_add(&c).unwrap()).unwrap();
        let right = a.poly_add(&b).unwrap().poly_add(&c).unwrap();

        assert_poly_eq(&left, &right, "DenseMle: (a+b)+c = a+(b+c)");
    }

    #[test]
    fn test_dense_mle_addition_commutativity() {
        let a = create_dense_mle_simple();
        let b = create_dense_mle_simple();

        let left = a.clone().poly_add(&b).unwrap();
        let right = b.poly_add(&a).unwrap();

        assert_poly_eq(&left, &right, "DenseMle: a+b = b+a");
    }

    #[test]
    fn test_dense_mle_addition_identity() {
        let a = create_dense_mle_simple();
        let num_vars = a.num_vars().unwrap();
        let zero_evals = vec![Fr::from(0u64); 1 << num_vars];
        let zero = PolyVariant::DenseMle(
            DenseMultilinearExtension::from_evaluations_vec(num_vars, zero_evals)
        );

        let result = a.clone().poly_add(&zero).unwrap();

        assert_poly_eq(&result, &a, "DenseMle: a+0 = a");
    }

    #[test]
    fn test_dense_mle_addition_inverse() {
        let a = create_dense_mle_simple();
        let num_vars = a.num_vars().unwrap();
        let zero_evals = vec![Fr::from(0u64); 1 << num_vars];
        let zero = PolyVariant::DenseMle(
            DenseMultilinearExtension::from_evaluations_vec(num_vars, zero_evals)
        );

        let neg_a = a.clone().poly_neg();
        let result = a.poly_add(&neg_a).unwrap();

        assert_poly_eq(&result, &zero, "DenseMle: a+(-a) = 0");
    }

    #[test]
    fn test_dense_mle_subtraction_as_inverse() {
        let a = create_dense_mle_simple();
        let b = create_dense_mle_simple();

        let sub_result = a.clone().poly_sub(&b).unwrap();
        let add_neg_result = a.poly_add(&b.poly_neg()).unwrap();

        assert_poly_eq(&sub_result, &add_neg_result, "DenseMle: a-b = a+(-b)");
    }

    #[test]
    fn test_dense_mle_multiplication_not_allowed() {
        let a = create_dense_mle_simple();
        let b = create_dense_mle_simple();

        let result = a.poly_mul(&b);

        assert!(result.is_err(), "DenseMle: multiplication should fail");
        assert!(matches!(result.unwrap_err(), PolyError::MleMultiplication));
    }

    // ========== Ring Axiom Tests: Sparse MLE ==========

    #[test]
    fn test_sparse_mle_addition_commutativity() {
        let a = create_sparse_mle_simple();
        let b = create_dense_mle_simple(); // Mix sparse and dense

        let left = a.clone().poly_add(&b).unwrap();
        let right = b.poly_add(&a).unwrap();

        assert_poly_eq(&left, &right, "SparseMle: a+b = b+a");
    }

    #[test]
    fn test_sparse_mle_addition_associativity() {
        let a = create_sparse_mle_simple();
        let b = create_dense_mle_simple();
        let c = create_sparse_mle_simple();

        let left = a.clone().poly_add(&b.clone().poly_add(&c).unwrap()).unwrap();
        let right = a.poly_add(&b).unwrap().poly_add(&c).unwrap();

        assert_poly_eq(&left, &right, "SparseMle: (a+b)+c = a+(b+c)");
    }

    // ========== Scalar Conversion Tests ==========

    #[test]
    fn test_scalar_to_poly_to_scalar_roundtrip() {
        let original = Fr::from(42u64);
        let poly = PolyVariant::from_scalar(original);
        let recovered = poly.to_scalar();

        assert_eq!(recovered, Some(original), "Scalar round-trip failed");
    }

    #[test]
    fn test_non_constant_poly_to_scalar_fails() {
        let poly = create_dense_uni_linear();
        let result = poly.to_scalar();

        assert!(result.is_none(), "Non-constant polynomial should not convert to scalar");
    }

    #[test]
    fn test_constant_dense_uni_to_scalar() {
        let coeffs = vec![Fr::from(42u64)];
        let poly = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs));
        let result = poly.to_scalar();

        assert_eq!(result, Some(Fr::from(42u64)), "Constant DenseUni should convert to scalar");
    }

    #[test]
    fn test_constant_sparse_uni_to_scalar() {
        let coeffs = vec![(0, Fr::from(42u64))];
        let poly = PolyVariant::SparseUni(SparsePolynomial::from_coefficients_vec(coeffs));
        let result = poly.to_scalar();

        assert_eq!(result, Some(Fr::from(42u64)), "Constant SparseUni should convert to scalar");
    }

    // ========== Mixed Type Tests ==========

    #[test]
    fn test_dense_sparse_uni_addition() {
        let dense = create_dense_uni_linear();
        let sparse = create_sparse_uni_linear();

        let result = dense.poly_add(&sparse).unwrap();

        // 2x+3 + 2x+3 = 4x+6
        let expected_coeffs = vec![Fr::from(6u64), Fr::from(4u64)];
        let expected = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(expected_coeffs));

        assert_poly_eq(&result, &expected, "Dense + Sparse should work");
    }

    #[test]
    fn test_dense_sparse_mle_addition() {
        let dense = create_dense_mle_simple();
        let sparse = create_sparse_mle_simple();

        let result = dense.poly_add(&sparse).unwrap();

        // [1,2,3,4] + [1,2,3,4] = [2,4,6,8]
        let expected_evals = vec![Fr::from(2u64), Fr::from(4u64), Fr::from(6u64), Fr::from(8u64)];
        let expected = PolyVariant::DenseMle(
            DenseMultilinearExtension::from_evaluations_vec(2, expected_evals)
        );

        assert_poly_eq(&result, &expected, "Dense MLE + Sparse MLE should work");
    }

    // ========== Zero and One Tests ==========

    #[test]
    fn test_zero_is_additive_identity() {
        let poly = create_dense_uni_quadratic();
        let zero = create_zero_uni();

        let result = poly.clone().poly_add(&zero).unwrap();
        assert_poly_eq(&result, &poly, "0 is additive identity");
    }

    #[test]
    fn test_one_is_multiplicative_identity() {
        let poly = create_dense_uni_quadratic();
        let one = create_one_uni();

        let result = poly.clone().poly_mul(&one).unwrap();
        assert_poly_eq(&result, &poly, "1 is multiplicative identity");
    }
}
