use super::utils::compute_chall;
use super::{
    data_structures::{Proof, VerifyingKey},
    Pari,
};
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use ark_ff::{FftField, Field, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{end_timer, ops::Neg, start_timer};
use super::{batch_inversion_and_mul, msm_bigint_wnaf};

impl<E: Pairing> Pari<E> {
    pub fn verify(proof: &Proof<E>, vk: &VerifyingKey<E>, instance_input: &[E::ScalarField]) -> bool
    where
        <E::G1Affine as AffineRepr>::BaseField: PrimeField,
        E::G1Affine: Neg<Output = E::G1Affine>,
    {
        let timer_verify =
            start_timer!(|| format!("Verification (|x|= {})", vk.succinct_index.instance_len));
        debug_assert_eq!(instance_input.len(), vk.succinct_index.instance_len - 1);
        let Proof { t_g, u_g, v_a, v_b } = proof;

        /////////////////////// Challenge Computation ///////////////////////
        let timer_transcript_init = start_timer!(|| "Computing Challenge");
        let challenge = compute_chall::<E>(vk, instance_input, t_g);
        end_timer!(timer_transcript_init);
        /////////////////////// Computing polynomials x_A ///////////////////////

        let timer_x_poly = start_timer!(|| "Compute x_a polynomial");
        let instance_size = vk.succinct_index.instance_len;
        let mut px_evaluations = Vec::with_capacity(instance_size);
        let r1cs_orig_num_cnstrs = vk.succinct_index.num_constraints - instance_size;

        px_evaluations.push(E::ScalarField::ONE);
        px_evaluations.extend_from_slice(&instance_input[..(instance_size - 1)]);
        let lag_coeffs_time = start_timer!(|| "Computing last lagrange coefficients");
        let (lagrange_coeffs, vanishing_poly_at_chall_inv) =
            Self::eval_last_lagrange_coeffs::<E::ScalarField>(
                &vk.domain,
                challenge,
                r1cs_orig_num_cnstrs,
                vk.succinct_index.instance_len,
            );
        end_timer!(lag_coeffs_time);
        #[cfg(feature = "sol")]
        {
            use crate::solidity::Solidifier;
            let mut solidifier = Solidifier::<E>::new();
            solidifier.set_vk(&vk);
            solidifier.set_proof(&proof);
            solidifier.set_input(instance_input);
            let (_, neg_h_i, nom_i) = Self::eval_last_lagrange_coeffs_traced::<E::ScalarField>(
                &vk.domain,
                challenge,
                r1cs_orig_num_cnstrs,
                vk.succinct_index.instance_len,
            );
            solidifier.coset_size = Some(vk.domain.size());
            solidifier.coset_offset = Some(vk.domain.coset_offset());
            solidifier.neg_h_gi = Some(neg_h_i);
            solidifier.nom_i = Some(nom_i);
            solidifier.minus_coset_offset_to_coset_size =
                Some(-(vk.domain.coset_offset().pow([vk.domain.size() as u64])));
            solidifier.coset_offset_to_coset_size_inverse =
                Some(E::ScalarField::ONE / vk.domain.evaluate_vanishing_polynomial(challenge));
            solidifier.solidify();
        }
        let x_a = lagrange_coeffs
            .into_iter()
            .zip(px_evaluations)
            .fold(E::ScalarField::zero(), |acc, (x, d)| acc + x * d);
        let z_a = x_a + v_a;
        end_timer!(timer_x_poly);

        /////////////////////// Computing the quotient evaluation///////////////////////

        let timer_q = start_timer!(|| "Computing the quotient evaluation");

        let v_q = (z_a * z_a - v_b) * vanishing_poly_at_chall_inv;
        end_timer!(timer_q);
        /////////////////////// Final Pairing///////////////////////

        let timer_scalar_mul = start_timer!(|| "Scalar mul");
        let right_second_left = msm_bigint_wnaf::<E::G1>(
            &[vk.alpha_g, vk.beta_g, vk.g, -*u_g],
            &[(*v_a).into(), (*v_b).into(), v_q.into(), challenge.into()],
        )
        .into();

        end_timer!(timer_scalar_mul);

        let timer_pairing = start_timer!(|| "Final Pairing");
        let right = E::multi_pairing(
            [*t_g, *u_g, right_second_left],
            [
                vk.delta_two_h_prep.clone(),
                vk.tau_h_prep.clone(),
                vk.h_prep.clone(),
            ],
        );
        assert!(right.is_zero());
        end_timer!(timer_pairing);
        end_timer!(timer_verify);
        true
    }

    #[cfg(feature = "sol")]
    fn eval_last_lagrange_coeffs_traced<F: FftField>(
        domain: &Radix2EvaluationDomain<F>,
        tau: F,
        start_ind: usize,
        count: usize,
    ) -> (Vec<F>, Vec<F>, Vec<F>)
    where
        E::BaseField: PrimeField + FftField,
        E::BaseField: FftField,
    {
        let size: usize = domain.size();
        let z_h_at_tau: F = domain.evaluate_vanishing_polynomial(tau);
        let mut neg_hi = Vec::new();
        let mut nom_i = Vec::new();
        let offset: F = domain.coset_offset();
        let group_gen: F = domain.group_gen();
        let _starting_g: F = offset * group_gen.pow([start_ind as u64]);
        let group_gen_inv = domain.group_gen_inv();
        let v_0_inv = domain.size_as_field_element() * offset.pow([size as u64 - 1]);
        let start_gen = group_gen.pow([start_ind as u64]);
        let mut l_i = z_h_at_tau.inverse().unwrap() * v_0_inv;
        let mut negative_cur_elem = (-offset) * (start_gen);
        let mut lagrange_coefficients_inverse = vec![F::zero(); count];
        for (_, coeff) in &mut lagrange_coefficients_inverse.iter_mut().enumerate() {
            neg_hi.push(negative_cur_elem);
            let nom = start_gen * (l_i.inverse().unwrap());
            nom_i.push(nom);
            let r_i = tau + negative_cur_elem;
            *coeff = l_i * r_i;
            l_i *= &group_gen_inv;
            negative_cur_elem *= &group_gen;
        }
        batch_inversion_and_mul(lagrange_coefficients_inverse.as_mut_slice(), &start_gen);
        (lagrange_coefficients_inverse, neg_hi, nom_i)
    }

    fn eval_last_lagrange_coeffs<F: FftField>(
        domain: &Radix2EvaluationDomain<F>,
        tau: F,
        start_ind: usize,
        count: usize,
    ) -> (Vec<F>, F) {
        let z_h_at_tau: F = domain.evaluate_vanishing_polynomial(tau);
        let group_gen: F = domain.group_gen();

        assert!(!z_h_at_tau.is_zero());

        let group_gen_inv = domain.group_gen_inv();
        let v_0_inv = domain.size_as_field_element();

        let start_gen = group_gen.pow([start_ind as u64]);
        let z_h_at_tau_inv = z_h_at_tau.inverse().unwrap();
        let mut l_i = z_h_at_tau_inv * v_0_inv;
        let mut negative_cur_elem = -start_gen;
        let mut lagrange_coefficients_inverse = vec![F::zero(); count];
        for coeff in &mut lagrange_coefficients_inverse.iter_mut() {
            *coeff = l_i * (tau + negative_cur_elem);
            l_i *= &group_gen_inv;
            negative_cur_elem *= &group_gen;
        }
        batch_inversion_and_mul(lagrange_coefficients_inverse.as_mut_slice(), &start_gen);
        (lagrange_coefficients_inverse, z_h_at_tau_inv)
    }
}
