use std::rc::Rc;

use ark_ec::{pairing::Pairing, scalar_mul::BatchMulPreprocessing};
use ark_ff::{Field, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

use super::{
    data_structures::{ProvingKey, SuccinctIndex, VerifyingKey},
    Pari,
};
use ark_relations::{
    gr1cs::{
        self,
        instance_outliner::{outline_sr1cs, InstanceOutliner},
        predicate::polynomial_constraint::SR1CS_PREDICATE_LABEL,
        ConstraintSynthesizer, ConstraintSystem, Matrix, OptimizationGoal, SynthesisError,
        SynthesisMode,
    },
    sr1cs::Sr1csAdapter,
};
use ark_ff::UniformRand;
use ark_std::{end_timer, rand::RngCore, start_timer, vec::Vec};

impl<E: Pairing> Pari<E> {
    pub fn keygen<C: ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
        circuit: C,
        rng: &mut R,
    ) -> (ProvingKey<E>, VerifyingKey<E>)
    where
        E: Pairing,
        E::ScalarField: Field,
    {
        let cs = Self::circuit_to_keygen_cs(circuit).unwrap();
        // Check if the constraint system has only one predicate which is Sqaured R1CS
        #[cfg(debug_assertions)]
        {
            assert_eq!(cs.num_predicates(), 1);
            assert_eq!(
                cs.num_constraints(),
                cs.get_predicate_num_constraints(SR1CS_PREDICATE_LABEL)
                    .unwrap()
            );
        }

        /////////////////////// Extract the constraint system  information ///////////////////////
        let instance_len = cs.num_instance_variables();
        let num_constraints = cs.num_constraints();
        /////////////////////// Generators ///////////////////////
        let timer_sample_generators = start_timer!(|| "Sample generators");

        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);
        end_timer!(timer_sample_generators);
        /////////////////////// Trapdoor generation ///////////////////////

        let timer_trapdoor_gen = start_timer!(|| "Trapdoor generation and exponentiations");
        let alpha = E::ScalarField::rand(rng);
        let beta = E::ScalarField::rand(rng);
        let delta_two = E::ScalarField::rand(rng);
        let tau = E::ScalarField::rand(rng);

        let alpha_g: <E as Pairing>::G1 = g * alpha;
        let beta_g = g * beta;
        let delta_two_h = h * delta_two;
        let tau_h = h * tau;

        let delta_two_inverse = delta_two.inverse().unwrap();

        let alpha_over_delta_two = alpha * delta_two_inverse;
        let beta_over_delta_two = beta * delta_two_inverse;
        end_timer!(timer_trapdoor_gen);

        /////////////////////// Computing the FFT domain ///////////////////////
        let timer_fft_domain = start_timer!(|| "Computing the FFT domain");
        let domain = Radix2EvaluationDomain::new(cs.num_constraints()).unwrap();
        assert_ne!(
            domain.evaluate_vanishing_polynomial(tau),
            E::ScalarField::zero()
        );
        end_timer!(timer_fft_domain);
        let domain_size = domain.size();
        let max_degree = domain_size - 1;
        /////////////////////// Computing {a_i(tau)}_{i=n+1}^{k}, {b_i(tau)}_{i=n+1}^{k} ////////////////////////
        let timer_compute_a_b = start_timer!(|| "Computing a_i(tau)'s and b_i(tau)'s");
        let (a, b) = Self::compute_ai_bi_at_tau(tau, &cs, domain).unwrap();
        end_timer!(timer_compute_a_b);
        /////////////////////// Succinct Index ///////////////////////
        let timer_succinct_index = start_timer!(|| "Generating Succinct Index");
        let num_instance_inputs = cs.num_instance_variables();
        let succinct_index = SuccinctIndex {
            num_constraints,
            instance_len,
        };
        end_timer!(timer_succinct_index);
        /////////////////////// interpolation Domain and powers of tau ///////////////////////
        //TODO: Find the correct len of powers of tau
        let timer_powers_of_tau = start_timer!(|| "Computing powers of tau");
        let mut powers_of_tau = vec![E::ScalarField::ONE];
        let mut cur = tau;
        for _ in 0..=max_degree {
            powers_of_tau.push(cur);
            cur *= &tau;
        }
        end_timer!(timer_powers_of_tau);
        /////////////////////// proving key generations ///////////////////////
        let timer_pk_gen = start_timer!(|| "Generating Proving Key");

        let timer_batch_mul_prep = start_timer!(|| "Batch Mul Preprocessing startup");
        let table = BatchMulPreprocessing::new(g, max_degree + 1);
        end_timer!(timer_batch_mul_prep);

        /////////////////////// Opening Keys ///////////////////////
        let timer_opening_keys = start_timer!(|| "Computing Opening Keys");

        /////////////////////// Sigma_a ///////////////////////
        // Construct sigma_a, It's denoted by sigma_a in the paper: step 7, fig 6, https://eprint.iacr.org/2024/1245.pdf
        // sigma_a = [(beta a_i(tau)/delta_1)G]_{i=1}^k
        let timer_sigma_a = start_timer!(|| "Computing sigma_a");
        let sigma_a_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * alpha)
            .collect::<Vec<_>>();
        let sigma_a = table.batch_mul(&sigma_a_powers);
        end_timer!(timer_sigma_a);

        /////////////////////// Sigma_b ///////////////////////
        // Construct sigma_b, It's denoted by sigma_b in the paper: step 7, fig 6, https://eprint.iacr.org/2024/1245.pdf
        // sigma_b = [(beta b_i(tau)/delta_1)G]_{i=1}^k
        let timer_sigma_b = start_timer!(|| "Computing sigma_b");
        let sigma_b_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|tau_to_i| *tau_to_i * beta)
            .collect::<Vec<_>>();
        let sigma_b = table.batch_mul(&sigma_b_powers);
        end_timer!(timer_sigma_b);

        /////////////////////// Sigma_q_opening ///////////////////////
        // Construct sigma_q_opening, It's denoted by sigma_q' in the paper: step 7, fig 6, https://eprint.iacr.org/2024/1245.pdf
        // sigma_q_opening = [(tau^i/delta_1)G]_{i=1}^k
        let timer_sigma_q_opening = start_timer!(|| "Computing sigma_q_opening");
        //TODO: Remove the bellow line
        let sigma_q_opening_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|tau| *tau)
            .collect::<Vec<_>>();
        let sigma_q_opening = table.batch_mul(&sigma_q_opening_powers);
        end_timer!(timer_sigma_q_opening);
        end_timer!(timer_opening_keys);

        /////////////////////// Commiting keys ///////////////////////

        let timer_commit_keys = start_timer!(|| "Computing Committing Keys");
        // Construct sigma, It's also denoted by sigma in the paper: step 6, fig 6, https://eprint.iacr.org/2024/1245.pdf
        // Sigma = [((alpha a_i(tau)+ beta b_(tau))/delta_2).G]_{i=n+1}^k
        let timer_sigma = start_timer!(|| "Computing sigma");
        let sigma_powers = a[num_instance_inputs..]
            .par_iter()
            .zip(&b[num_instance_inputs..])
            .map(|(a_i, b_i)| *a_i * alpha_over_delta_two + *b_i * beta_over_delta_two)
            // .map(|(a_i, b_i)|  *a_i * alpha_over_delta_two + *b_i * beta_over_delta_two)
            .collect::<Vec<_>>();
        let sigma = table.batch_mul(&sigma_powers);
        end_timer!(timer_sigma);

        // Construct sigma_q_comm, It's denoted by sigma_q in the paper: step 6, fig 6, https://eprint.iacr.org/2024/1245.pdf
        // sigma_q = [(tau^i/delta_2)G]_{i=1}^m
        let timer_q_comm = start_timer!(|| "Computing sigma_q_comm");
        let sigma_q_comm_powers = powers_of_tau[0..max_degree]
            .par_iter()
            .map(|tau| *tau * delta_two_inverse)
            .collect::<Vec<_>>();
        let sigma_q_comm = table.batch_mul(&sigma_q_comm_powers);
        end_timer!(timer_q_comm);
        end_timer!(timer_commit_keys);
        end_timer!(timer_pk_gen);
        // Output the verifying key: step 8, fig 6, https://eprint.iacr.org/2024/1245.pdf
        let vk = VerifyingKey {
            succinct_index,
            alpha_g: alpha_g.into(),
            beta_g: beta_g.into(),
            delta_two_h_prep: delta_two_h.into().into(),
            delta_two_h: delta_two_h.into(),
            tau_h: tau_h.into(),
            tau_h_prep: tau_h.into().into(),
            g: g.into(),
            h_prep: h.into().into(),
            h: h.into(),
            domain,
        };

        // Output the proving key: step 8, fig 6, https://eprint.iacr.org/2024/1245.pdf
        let pk = ProvingKey {
            sigma,
            sigma_a,
            sigma_b,
            sigma_q_comm,
            sigma_q_opening,
            verifying_key: vk.clone(),
        };

        (pk, vk)
    }

    pub fn circuit_to_keygen_cs<C: ConstraintSynthesizer<E::ScalarField>>(
        circuit: C,
    ) -> Result<ConstraintSystem<E::ScalarField>, SynthesisError>
    where
        E: Pairing,
        E::ScalarField: Field,
        E::ScalarField: std::convert::From<i32>,
    {
        // Start up the constraint System and synthesize the circuit
        let timer_cs_startup = start_timer!(|| "Constraint System Startup");
        let cs: gr1cs::ConstraintSystemRef<E::ScalarField> = ConstraintSystem::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let sr1cs_cs = Sr1csAdapter::r1cs_to_sr1cs(&cs).unwrap();
        sr1cs_cs.set_instance_outliner(InstanceOutliner {
            pred_label: SR1CS_PREDICATE_LABEL.to_string(),
            func: Rc::new(outline_sr1cs),
        });
        let timer_synthesize_circuit = start_timer!(|| "Synthesize Circuit");
        end_timer!(timer_synthesize_circuit);

        let timer_inlining = start_timer!(|| "Inlining constraints");
        // sr1cs_cs.finalize();
        let mut sr1cs_inner = sr1cs_cs.into_inner().unwrap();
        let _ = sr1cs_inner.perform_instance_outlining(InstanceOutliner {
            pred_label: SR1CS_PREDICATE_LABEL.to_string(),
            func: Rc::new(outline_sr1cs),
        });
        end_timer!(timer_inlining);
        end_timer!(timer_cs_startup);
        Ok(sr1cs_inner)
    }

    #[allow(clippy::type_complexity)]
    fn compute_ai_bi_at_tau(
        tau: E::ScalarField,
        new_cs: &ConstraintSystem<E::ScalarField>,
        domain: Radix2EvaluationDomain<E::ScalarField>,
    ) -> Result<(Vec<E::ScalarField>, Vec<E::ScalarField>), SynthesisError> {
        // Compute all the lagrange polynomials
        let timer_eval_all_lagrange_polys = start_timer!(|| "Evaluating all Lagrange polys");
        let lagrange_polys_at_tau = domain.evaluate_all_lagrange_coefficients(tau);
        end_timer!(timer_eval_all_lagrange_polys);

        let num_variables = new_cs.num_instance_variables() + new_cs.num_witness_variables();
        let num_constraints = new_cs.num_constraints();
        let matrices = &new_cs.to_matrices().unwrap()[SR1CS_PREDICATE_LABEL];

        let mut a = vec![E::ScalarField::zero(); num_variables];
        let mut b = vec![E::ScalarField::zero(); num_variables];

        let timer_compute_a_b = start_timer!(|| "Compute a_i(tau)'s and z_i(tau)'s");
        for (i, u_i) in lagrange_polys_at_tau
            .iter()
            .enumerate()
            .take(num_constraints)
        {
            for &(ref coeff, index) in &matrices[0][i] {
                a[index] += &(*u_i * coeff);
            }
            for &(ref coeff, index) in &matrices[1][i] {
                b[index] += &(*u_i * coeff);
            }
        }
        // write a sanity check, make up a z, check if MV product is correct
        end_timer!(timer_compute_a_b);
        Ok((a, b))
    }

    /// Keygen entry point that takes raw SR1CS matrices instead of a
    /// `ConstraintSynthesizer`. Bypasses circuit synthesis and the
    /// `Sr1csAdapter` R1CS→SR1CS conversion, so the resulting (pk, vk)
    /// matches a benchmark instance built directly in SR1CS form. Used by
    /// the bench harness so the native side proves the same SR1CS
    /// statement the zippel side does (no expansion of constraint count
    /// or aux variables from the R1CS adapter).
    pub fn keygen_from_sr1cs<R: RngCore>(
        a_mat: &Matrix<E::ScalarField>,
        b_mat: &Matrix<E::ScalarField>,
        instance_len: usize,
        num_vars: usize,
        rng: &mut R,
    ) -> (ProvingKey<E>, VerifyingKey<E>)
    where
        E::ScalarField: Field,
    {
        let num_constraints = a_mat.len();
        assert_eq!(b_mat.len(), num_constraints, "A and B row counts must match");

        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);

        let alpha = E::ScalarField::rand(rng);
        let beta = E::ScalarField::rand(rng);
        let delta_two = E::ScalarField::rand(rng);
        let tau = E::ScalarField::rand(rng);

        let alpha_g: E::G1 = g * alpha;
        let beta_g = g * beta;
        let delta_two_h = h * delta_two;
        let tau_h = h * tau;

        let delta_two_inverse = delta_two.inverse().unwrap();
        let alpha_over_delta_two = alpha * delta_two_inverse;
        let beta_over_delta_two = beta * delta_two_inverse;

        let domain = Radix2EvaluationDomain::<E::ScalarField>::new(num_constraints).unwrap();
        assert_ne!(
            domain.evaluate_vanishing_polynomial(tau),
            E::ScalarField::zero()
        );
        let domain_size = domain.size();
        let max_degree = domain_size - 1;

        // a_i(tau), b_i(tau) for i = 0..num_vars.
        let lagrange_polys_at_tau = domain.evaluate_all_lagrange_coefficients(tau);
        let mut a = vec![E::ScalarField::zero(); num_vars];
        let mut b = vec![E::ScalarField::zero(); num_vars];
        for (i, u_i) in lagrange_polys_at_tau
            .iter()
            .enumerate()
            .take(num_constraints)
        {
            for &(ref coeff, index) in &a_mat[i] {
                a[index] += *u_i * coeff;
            }
            for &(ref coeff, index) in &b_mat[i] {
                b[index] += *u_i * coeff;
            }
        }

        let mut powers_of_tau = vec![E::ScalarField::ONE];
        let mut cur = tau;
        for _ in 0..=max_degree {
            powers_of_tau.push(cur);
            cur *= &tau;
        }

        let table = BatchMulPreprocessing::new(g, max_degree + 1);

        let sigma_a_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|t| *t * alpha)
            .collect::<Vec<_>>();
        let sigma_a = table.batch_mul(&sigma_a_powers);

        let sigma_b_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .map(|t| *t * beta)
            .collect::<Vec<_>>();
        let sigma_b = table.batch_mul(&sigma_b_powers);

        let sigma_q_opening_powers = powers_of_tau[0..max_degree + 1]
            .par_iter()
            .copied()
            .collect::<Vec<_>>();
        let sigma_q_opening = table.batch_mul(&sigma_q_opening_powers);

        let sigma_powers = a[instance_len..]
            .par_iter()
            .zip(&b[instance_len..])
            .map(|(a_i, b_i)| *a_i * alpha_over_delta_two + *b_i * beta_over_delta_two)
            .collect::<Vec<_>>();
        let sigma = table.batch_mul(&sigma_powers);

        let sigma_q_comm_powers = powers_of_tau[0..max_degree]
            .par_iter()
            .map(|t| *t * delta_two_inverse)
            .collect::<Vec<_>>();
        let sigma_q_comm = table.batch_mul(&sigma_q_comm_powers);

        let succinct_index = SuccinctIndex {
            num_constraints,
            instance_len,
        };

        let vk = VerifyingKey {
            succinct_index,
            alpha_g: alpha_g.into(),
            beta_g: beta_g.into(),
            delta_two_h_prep: delta_two_h.into().into(),
            delta_two_h: delta_two_h.into(),
            tau_h: tau_h.into(),
            tau_h_prep: tau_h.into().into(),
            g: g.into(),
            h_prep: h.into().into(),
            h: h.into(),
            domain,
        };

        let pk = ProvingKey {
            sigma,
            sigma_a,
            sigma_b,
            sigma_q_comm,
            sigma_q_opening,
            verifying_key: vk.clone(),
        };

        (pk, vk)
    }
}
