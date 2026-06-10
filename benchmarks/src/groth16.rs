//! Groth16 comparison: zippel-compiled Groth16 (BLS12-381) vs. a
//! vendored native Groth16 prover/verifier, both running against
//! backend's git-main arkworks. Both sides prove
//!
//! ```text
//! e(A, B) == e(α, β) · e(IC, γ) · e(C, δ)
//! ```
//!
//! Parity decisions:
//!   - The zippel side uses `examples/groth16/groth16.zippel`
//!     (h_coeffs supplied externally) and folds the witness-map
//!     `h_coeffs` computation into its prove timer, matching the
//!     vendored native prover which does the same.
//!   - Both sides consume the same `GitKeys` (proving/verifying-key
//!     fields translated from v0.5 ark-groth16 setup output via canonical
//!     bytes) and the same git-main `(matrices, instance, witness)`. So
//!     all timed work uses the same MSM (`ark_ec::VariableBaseMSM`) and
//!     pairing (`Pairing::multi_pairing`) implementations as zippel —
//!     no v0.5 vs. git-main library asymmetry.
//!   - The ark-groth16 v0.5 keygen still runs untimed at setup, because
//!     re-implementing the Lagrange-basis (αu_i + βv_i + w_i)/γ key
//!     construction is ~200 lines of well-tested upstream code and
//!     doesn't affect the comparison.
//!
//! Size knob: `log_constraints = log_2(num_constraints)`. The bench
//! circuit is a squaring chain (`w[i+1] = w[i] * w[i]`) emitting one
//! constraint per row, one witness per row, and a single public output
//! (the final value). So `num_inputs = 2` (constant 1 + the output)
//! and `num_witnesses = num_constraints`, giving near-square R1CS
//! matrices N × (N+2). Fixed M means the verifier's public-input
//! absorption cost is O(1) in N, matching how Groth16 is used in
//! practice (e.g., proving knowledge of a preimage with a fixed-size
//! digest as the public statement).

use crate::Timing;

pub const DEFAULT_LOG_CONSTRAINTS: usize = 10;

// ---------------------------------------------------------------------------
// Shared setup: BenchCircuit + keys + witness/matrices/h_coeffs, all in
// 0.6 arkworks types (same set the zippel side uses). The `bridge`
// module below still exists as a thin re-shaper of `Shared` into the
// flat `Translated` view both sides consume — its byte round-trip is now
// identity since shared and bridge share the same arkworks version.
// ---------------------------------------------------------------------------

pub mod shared {
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::UniformRand;
    use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
    use ark_relations::gr1cs::{
        predicate::polynomial_constraint::R1CS_PREDICATE_LABEL, ConstraintSynthesizer,
        ConstraintSystem, ConstraintSystemRef, LinearCombination, Matrix, SynthesisError,
        SynthesisMode,
    };

    pub type E = Bls12_381;
    pub type F = Fr;

    /// Bench circuit: a squaring chain producing one public output.
    ///
    /// Layout with `num_constraints = N`:
    ///   * 1 public input  (`y` = final squared value, M=2 incl. constant 1)
    ///   * N witness vars  (`w[0..N]`, with `w[0]` a random seed)
    ///   * N constraints:
    ///       row i in [0, N-2]:  w[i] * w[i] = w[i+1]
    ///       row N-1:            w[N-1] * w[N-1] = y
    ///
    /// R1CS matrices are N × (N+2) — near-square (vs. the prior
    /// N × (3N+1) shape). Crucially, **M is constant in N** so the
    /// verifier's public-input absorption cost is O(1), making the
    /// verify-side numbers reflect "Groth16 as actually deployed"
    /// rather than the degenerate "every output is public" case.
    #[derive(Clone)]
    pub struct BenchCircuit {
        pub num_constraints: usize,
    }

    impl ConstraintSynthesizer<F> for BenchCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            // Deterministic randomness so the assignment is reproducible
            // across the two `generate_constraints` calls (setup + matrix
            // capture).
            let mut rng = ark_std_test_rng_seeded(self.num_constraints as u64);
            let n = self.num_constraints;

            // Compute witness values up-front so we can allocate the
            // single public output before declaring witnesses (matches
            // ark-relations' convention: instance vars come first).
            let w0 = F::rand(&mut rng);
            let mut wit_vals = Vec::with_capacity(n);
            let mut cur = w0;
            for _ in 0..n {
                wit_vals.push(cur);
                cur = cur * cur;
            }
            let y_val = cur; // = w0^(2^N)

            // 1 public output.
            let y = cs.new_input_variable(|| Ok(y_val))?;

            // N witness vars.
            let mut wit_vars = Vec::with_capacity(n);
            for v in &wit_vals {
                wit_vars.push(cs.new_witness_variable(|| Ok(*v))?);
            }

            // N squaring constraints, the last one binding to `y`.
            // gr1cs takes closures returning a LinearCombination —
            // captures avoid building the LCs unless the predicate needs
            // them (cf. enforce_constraint in 0.5 r1cs which took LCs
            // directly).
            for i in 0..n {
                let wi = wit_vars[i];
                let next_var = if i + 1 < n { wit_vars[i + 1] } else { y };
                cs.enforce_r1cs_constraint(
                    || LinearCombination::from(wi),
                    || LinearCombination::from(wi),
                    || LinearCombination::from(next_var),
                )?;
            }
            Ok(())
        }
    }

    /// Seeded RNG (via ark_std), so two independent `generate_constraints`
    /// calls with the same `num_constraints` produce the same instance +
    /// witness assignments.
    fn ark_std_test_rng_seeded(seed: u64) -> ark_std::rand::rngs::StdRng {
        use ark_std::rand::SeedableRng;
        let mut seed_bytes = [0u8; 32];
        seed_bytes[..8].copy_from_slice(&seed.to_le_bytes());
        ark_std::rand::rngs::StdRng::from_seed(seed_bytes)
    }

    /// Captures the 0.6 keygen output + R1CS matrices + assignment for
    /// one circuit size. Both sides translate from here.
    ///
    /// `matrices` is the gr1cs R1CS-predicate matrix triple, indexed as
    /// `[0]=A, [1]=B, [2]=C` (in 0.5 r1cs the equivalent was a struct
    /// with `.a/.b/.c` fields).
    pub struct Shared {
        pub pk: ProvingKey<E>,
        pub vk: VerifyingKey<E>,
        pub matrices: Vec<Matrix<F>>,
        pub num_inputs: usize,
        pub num_constraints: usize,
        pub instance_assignment: Vec<F>,
        pub witness_assignment: Vec<F>,
    }

    pub fn build(num_constraints: usize) -> Shared {
        let mut setup_rng = ark_std_test_rng_seeded(0xC0FFEE_u64 ^ num_constraints as u64);
        let circuit = BenchCircuit { num_constraints };
        let pk = Groth16::<E>::generate_random_parameters_with_reduction(
            circuit.clone(),
            &mut setup_rng,
        )
        .expect("groth16 setup");
        let vk = pk.vk.clone();

        // Capture the matrices + assignment by replaying the synthesizer in
        // Prove mode. Same seed inside the circuit → same witness values.
        // gr1cs uses generalized predicates; we pull the standard R1CS
        // matrix triple via R1CS_PREDICATE_LABEL.
        let cs = ConstraintSystem::<F>::new_ref();
        cs.set_mode(SynthesisMode::Prove {
            construct_matrices: true,
            generate_lc_assignments: true,
        });
        circuit
            .clone()
            .generate_constraints(cs.clone())
            .expect("synthesizer");
        cs.finalize();
        let mut predicate_matrices = cs.to_matrices().expect("matrices");
        let matrices = predicate_matrices
            .remove(R1CS_PREDICATE_LABEL)
            .expect("R1CS predicate matrices");
        let cs_borrowed = cs.borrow().expect("borrow cs");
        let num_inputs = cs_borrowed.num_instance_variables();
        let num_constraints_real = cs_borrowed.num_constraints();
        let instance_assignment = cs_borrowed
            .instance_assignment()
            .expect("instance assignment")
            .to_vec();
        let witness_assignment = cs_borrowed
            .witness_assignment()
            .expect("witness assignment")
            .to_vec();
        drop(cs_borrowed);

        Shared {
            pk,
            vk,
            matrices,
            num_inputs,
            num_constraints: num_constraints_real,
            instance_assignment,
            witness_assignment,
        }
    }
}

// ---------------------------------------------------------------------------
// Bridge: re-shape `Shared` into the flat `Translated` view that both the
// zippel and native sides consume. After the 0.6 migration this is a
// pure field projection — `Shared` and `Translated` are over the same
// arkworks 0.6 types — but we keep the layer so downstream call sites
// (zippel_side / native_side, witness_map, build_translated) stay
// stable. The byte-roundtrip helpers are now identity / Affine→Projective.
// ---------------------------------------------------------------------------

pub mod bridge {
    use super::shared::Shared;
    use ark_bls12_381::{Bls12_381, Fr as GitFr, G1Projective as GitG1Proj, G2Projective as GitG2Proj};
    use ark_ec::{pairing::Pairing, AffineRepr as GitAffineRepr};
    use ark_ff::{FftField, Field, Zero};
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

    type NpG1Affine = <Bls12_381 as Pairing>::G1Affine;
    type NpG2Affine = <Bls12_381 as Pairing>::G2Affine;

    pub fn fr_to_git(x: &GitFr) -> GitFr { *x }

    pub fn fr_vec_to_git(xs: &[GitFr]) -> Vec<GitFr> { xs.to_vec() }

    pub fn g1_to_git_proj(p: &NpG1Affine) -> GitG1Proj { p.into_group() }

    pub fn g2_to_git_proj(p: &NpG2Affine) -> GitG2Proj { p.into_group() }

    pub fn g1_vec_to_git(ps: &[NpG1Affine]) -> Vec<GitG1Proj> {
        ps.iter().map(g1_to_git_proj).collect()
    }

    pub fn g2_vec_to_git(ps: &[NpG2Affine]) -> Vec<GitG2Proj> {
        ps.iter().map(g2_to_git_proj).collect()
    }

    /// Proving + verifying key fields, projected into git-main BLS12-381.
    pub struct GitKeys {
        pub alpha_g1: GitG1Proj,
        pub beta_g1: GitG1Proj,
        pub beta_g2: GitG2Proj,
        pub gamma_g2: GitG2Proj,
        pub delta_g1: GitG1Proj,
        pub delta_g2: GitG2Proj,
        pub a_query: Vec<GitG1Proj>,
        pub b_g1_query: Vec<GitG1Proj>,
        pub b_g2_query: Vec<GitG2Proj>,
        pub h_query: Vec<GitG1Proj>,
        pub l_query: Vec<GitG1Proj>,
        pub gamma_abc_g1: Vec<GitG1Proj>,
    }

    /// Constraint matrices, projected into git-main field.
    pub struct GitMatrices {
        pub a: Vec<Vec<(GitFr, usize)>>,
        pub b: Vec<Vec<(GitFr, usize)>>,
        pub c: Vec<Vec<(GitFr, usize)>>,
    }

    /// All inputs both sides need, expressed entirely in git-main types.
    pub struct Translated {
        pub keys: GitKeys,
        pub mat: GitMatrices,
        pub instance_assignment: Vec<GitFr>,
        pub witness_assignment: Vec<GitFr>,
        pub full_assignment: Vec<GitFr>,
        pub num_inputs: usize,
        pub num_constraints: usize,
        /// Size of `pk.h_query` (= domain.size() − 1).
        pub h_size: usize,
        /// `vk.gamma_abc_g1.len()` (= num_inputs).
        pub m: usize,
        /// `pk.l_query.len()` (= num_witness_aux variables).
        pub l: usize,
    }

    pub fn translate_shared(s: &Shared) -> Translated {
        let keys = GitKeys {
            alpha_g1: g1_to_git_proj(&s.pk.vk.alpha_g1),
            beta_g1: g1_to_git_proj(&s.pk.beta_g1),
            beta_g2: g2_to_git_proj(&s.pk.vk.beta_g2),
            gamma_g2: g2_to_git_proj(&s.pk.vk.gamma_g2),
            delta_g1: g1_to_git_proj(&s.pk.delta_g1),
            delta_g2: g2_to_git_proj(&s.pk.vk.delta_g2),
            a_query: g1_vec_to_git(&s.pk.a_query),
            b_g1_query: g1_vec_to_git(&s.pk.b_g1_query),
            b_g2_query: g2_vec_to_git(&s.pk.b_g2_query),
            h_query: g1_vec_to_git(&s.pk.h_query),
            l_query: g1_vec_to_git(&s.pk.l_query),
            gamma_abc_g1: g1_vec_to_git(&s.vk.gamma_abc_g1),
        };
        // gr1cs ConstraintMatrices is Vec<Matrix<F>> — [0]=A, [1]=B, [2]=C
        // for the R1CS predicate. (In 0.5 r1cs the same struct exposed
        // .a/.b/.c fields; the 0.6 gr1cs view goes by index.)
        let translate_row = |row: &Vec<(GitFr, usize)>| row.clone();
        let mat = GitMatrices {
            a: s.matrices[0].iter().map(translate_row).collect(),
            b: s.matrices[1].iter().map(translate_row).collect(),
            c: s.matrices[2].iter().map(translate_row).collect(),
        };
        let instance_assignment = fr_vec_to_git(&s.instance_assignment);
        let witness_assignment = fr_vec_to_git(&s.witness_assignment);
        let full_assignment = {
            let mut v = instance_assignment.clone();
            v.extend(witness_assignment.iter().copied());
            v
        };
        Translated {
            keys,
            mat,
            instance_assignment,
            witness_assignment,
            full_assignment,
            num_inputs: s.num_inputs,
            num_constraints: s.num_constraints,
            h_size: s.pk.h_query.len(),
            m: s.vk.gamma_abc_g1.len(),
            l: s.pk.l_query.len(),
        }
    }

    /// R1CS-to-QAP witness map at git-main types — same algorithm as
    /// ark-groth16's `LibsnarkReduction::witness_map_from_matrices`. Both
    /// the zippel-side and the vendored native prover call this inside
    /// their prove timer.
    pub fn witness_map(
        mat: &GitMatrices,
        num_inputs: usize,
        num_constraints: usize,
        full_assignment: &[GitFr],
    ) -> Vec<GitFr> {
        let zero = GitFr::zero();
        let domain_size = num_constraints + num_inputs;
        let domain =
            GeneralEvaluationDomain::<GitFr>::new(domain_size).expect("domain for witness map");
        let domain_size = domain.size();

        // A·z, B·z on the constraint domain, padded out to domain_size.
        let mut a = vec![zero; domain_size];
        let mut b = vec![zero; domain_size];
        for (i, row) in mat.a.iter().enumerate() {
            for (c, j) in row {
                a[i] += *c * full_assignment[*j];
            }
        }
        for (i, row) in mat.b.iter().enumerate() {
            for (c, j) in row {
                b[i] += *c * full_assignment[*j];
            }
        }
        // Libsnark reduction folds identity rows for the first
        // `num_inputs` instance positions into A at the constraint-domain
        // tail: A[constraints + i] = e_i. Mirror that so the QAP relation
        // matches the keys.
        for i in 0..num_inputs {
            a[num_constraints + i] = full_assignment[i];
        }

        domain.ifft_in_place(&mut a);
        domain.ifft_in_place(&mut b);
        let coset = domain.get_coset(GitFr::GENERATOR).expect("coset");
        coset.fft_in_place(&mut a);
        coset.fft_in_place(&mut b);

        let mut c = vec![zero; domain_size];
        for (i, row) in mat.c.iter().enumerate() {
            for (cc, j) in row {
                c[i] += *cc * full_assignment[*j];
            }
        }
        domain.ifft_in_place(&mut c);
        coset.fft_in_place(&mut c);

        // V_H(x) = x^N − 1; constant on the coset, evaluated via the
        // ORIGINAL domain at the coset offset g.
        let v_h_inv = domain
            .evaluate_vanishing_polynomial(GitFr::GENERATOR)
            .inverse()
            .expect("V_H(g) inverse");
        for i in 0..domain_size {
            a[i] = (a[i] * b[i] - c[i]) * v_h_inv;
        }
        coset.ifft_in_place(&mut a);
        a
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn fr_roundtrips() {
            use ark_ff::UniformRand;
            let mut rng = ark_std::test_rng();
            let x = GitFr::rand(&mut rng);
            let _y = fr_to_git(&x);
        }
    }
}

// ---------------------------------------------------------------------------
// Zippel side: compile groth16.zippel, feed translated inputs, time
// prove + verify. Prove timer includes `bridge::witness_map` to match the
// vendored native prover.
// ---------------------------------------------------------------------------

pub mod zippel_side {
    use super::Timing;
    use super::bridge::{Translated, witness_map};
    use ark_bls12_381::{Fr as GitFr, G1Projective, G2Projective};
    use ark_ec::CurveGroup;
    use ark_ff::Zero;
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup<'a> {
        handler: ZippelHandler<ArkBls12_381>,
        inputs_base: Ctx<Vid, Value<ArkBls12_381>>,
        public_inputs: Ctx<Vid, Value<ArkBls12_381>>,
        translated: &'a Translated,
    }

    impl<'a> Setup<'a> {
        pub fn new(translated: &'a Translated) -> Self {
            // Pre-affinize the query vectors ONCE here, then feed them as
            // `Value::VecG{1,2}Affine`. The `dot(VecG_, VecScalar)` arms
            // in backend/src/values.rs have separate dispatch paths:
            //   - VecG_       → calls `normalize_batch` every prove call
            //                   (1 inv + ~3N muls, scales with circuit size)
            //   - VecG_Affine → skips conversion entirely, straight to MSM
            // Native already pays this cost once via `AffineKeys::from`
            // outside its timer; this mirrors that to keep the comparison
            // honest (prove-timer measures the SNARK, not affine setup).
            let keys = &translated.keys;
            let a_query_aff = G1Projective::normalize_batch(&keys.a_query);
            let b_g1_query_aff = G1Projective::normalize_batch(&keys.b_g1_query);
            let b_g2_query_aff = G2Projective::normalize_batch(&keys.b_g2_query);
            let h_query_aff = G1Projective::normalize_batch(&keys.h_query);
            let l_query_aff = G1Projective::normalize_batch(&keys.l_query);
            let gamma_abc_aff = G1Projective::normalize_batch(&keys.gamma_abc_g1);

            let inputs_base = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("alpha_g1".to_string()), Value::G1(keys.alpha_g1)),
                (Vid("beta_g2".to_string()), Value::G2(keys.beta_g2)),
                (Vid("gamma_g2".to_string()), Value::G2(keys.gamma_g2)),
                (Vid("delta_g2".to_string()), Value::G2(keys.delta_g2)),
                (
                    Vid("gamma_abc_g1".to_string()),
                    Value::VecG1Affine(gamma_abc_aff),
                ),
                (Vid("beta_g1".to_string()), Value::G1(keys.beta_g1)),
                (Vid("delta_g1".to_string()), Value::G1(keys.delta_g1)),
                (
                    Vid("a_query".to_string()),
                    Value::VecG1Affine(a_query_aff),
                ),
                (
                    Vid("b_g1_query".to_string()),
                    Value::VecG1Affine(b_g1_query_aff),
                ),
                (
                    Vid("b_g2_query".to_string()),
                    Value::VecG2Affine(b_g2_query_aff),
                ),
                (
                    Vid("h_query".to_string()),
                    Value::VecG1Affine(h_query_aff),
                ),
                (
                    Vid("l_query".to_string()),
                    Value::VecG1Affine(l_query_aff),
                ),
                (
                    Vid("instance_assignment".to_string()),
                    Value::VecScalar(translated.instance_assignment.clone()),
                ),
                (
                    Vid("witness_assignment".to_string()),
                    Value::VecScalar(translated.witness_assignment.clone()),
                ),
            ]);

            // Only verifier-relevant inputs: alpha_g1, beta_g2, gamma_g2,
            // delta_g2 appear in the pairing equation; gamma_abc_g1 + the
            // public instance_assignment build IC. beta_g1, delta_g1,
            // a_query, b_g1_query, b_g2_query, h_query, l_query are
            // prover-only (now `private` in the proto), so they must NOT
            // be in the verifier's input ctx — absorbing them into FS
            // would dominate verify time at large M+L.
            let public_input_names = [
                "alpha_g1",
                "beta_g2",
                "gamma_g2",
                "delta_g2",
                "gamma_abc_g1",
                "instance_assignment",
            ];
            let public_inputs: Ctx<Vid, Value<ArkBls12_381>> = inputs_base
                .clone()
                .into_iter()
                .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
                .collect();

            let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("M"), &translated.m);
            sizes.insert(&Tid::new("L"), &translated.l);
            sizes.insert(&Tid::new("H"), &translated.h_size);
            handler.compile(&sizes);

            Setup {
                handler,
                inputs_base,
                public_inputs,
                translated,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            let prover_scheduled = self.handler.default_schedule_prover();

            let t = Instant::now();
            let mut h_coeffs = witness_map(
                &self.translated.mat,
                self.translated.num_inputs,
                self.translated.num_constraints,
                &self.translated.full_assignment,
            );
            h_coeffs.resize(self.translated.h_size, GitFr::zero());
            let mut inputs = self.inputs_base.clone();
            inputs.insert(&Vid("h_coeffs".to_string()), &Value::VecScalar(h_coeffs));
            let proof = self
                .handler
                .run_prover(prover_scheduled, inputs)
                .expect("zippel groth16 prover failed");
            let prove = t.elapsed();

            self.handler.set_public_inputs(self.public_inputs.clone());
            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("zippel groth16 verifier failed");
            let verify = t.elapsed();
            let result = check_verification(verifier_result);
            assert!(result.passed, "zippel Groth16 verification FAILED");

            Timing { prove, verify }
        }
    }
}

// ---------------------------------------------------------------------------
// Native side: vendored Groth16 prover + verifier against git-main
// arkworks. Same MSM (`ark_ec::VariableBaseMSM`) and pairing
// (`Bls12_381::multi_pairing`) implementations the zippel backend uses.
// ---------------------------------------------------------------------------

pub mod native_side {
    use super::Timing;
    use super::bridge::{Translated, witness_map};
    use ark_bls12_381::{Bls12_381 as GitBls12_381, Fr as GitFr, G1Projective, G2Projective};
    use ark_ec::CurveGroup;
    use ark_ec::pairing::Pairing;
    use ark_ec::{AffineRepr, VariableBaseMSM};
    use ark_ff::{PrimeField, UniformRand};
    use std::time::{Duration, Instant};

    type E = GitBls12_381;
    type G1Affine = <E as Pairing>::G1Affine;
    type G2Affine = <E as Pairing>::G2Affine;

    /// Cached affine views of the proving-key MSM bases. Affine form is
    /// what `VariableBaseMSM::msm_bigint` consumes, so we pay the
    /// `normalize_batch` cost once at setup rather than on every prove.
    pub struct AffineKeys {
        alpha_g1: G1Affine,
        beta_g1: G1Affine,
        beta_g2_aff: G2Affine,
        gamma_g2_aff: G2Affine,
        delta_g1: G1Affine,
        delta_g2_aff: G2Affine,
        a_query: Vec<G1Affine>,
        b_g1_query: Vec<G1Affine>,
        b_g2_query: Vec<G2Affine>,
        h_query: Vec<G1Affine>,
        l_query: Vec<G1Affine>,
        gamma_abc_g1: Vec<G1Affine>,
    }

    impl AffineKeys {
        pub fn from(translated: &Translated) -> Self {
            let keys = &translated.keys;
            AffineKeys {
                alpha_g1: keys.alpha_g1.into_affine(),
                beta_g1: keys.beta_g1.into_affine(),
                beta_g2_aff: keys.beta_g2.into_affine(),
                gamma_g2_aff: keys.gamma_g2.into_affine(),
                delta_g1: keys.delta_g1.into_affine(),
                delta_g2_aff: keys.delta_g2.into_affine(),
                a_query: G1Projective::normalize_batch(&keys.a_query),
                b_g1_query: G1Projective::normalize_batch(&keys.b_g1_query),
                b_g2_query: G2Projective::normalize_batch(&keys.b_g2_query),
                h_query: G1Projective::normalize_batch(&keys.h_query),
                l_query: G1Projective::normalize_batch(&keys.l_query),
                gamma_abc_g1: G1Projective::normalize_batch(&keys.gamma_abc_g1),
            }
        }
    }

    pub struct Setup<'a> {
        translated: &'a Translated,
        keys: AffineKeys,
    }

    impl<'a> Setup<'a> {
        pub fn new(translated: &'a Translated) -> Self {
            Setup {
                translated,
                keys: AffineKeys::from(translated),
            }
        }

        /// Time the sparse matrix–vector products the native prover does
        /// inside `bridge::witness_map` (A·z, B·z, C·z over the
        /// constraint domain — the FFTs that follow are part of the QAP
        /// step proper and stay counted). The .zippel circuit does NOT
        /// compute these matvecs (h_coeffs is provided as input), so for
        /// a parity comparison of the SNARK-specific work, this MVM cost
        /// is subtracted from the native prove time. Caveat: zippel-side
        /// `time_protocol` still calls `bridge::witness_map` in Rust
        /// before handing off to the runtime, so its prove timer still
        /// includes this MVM. Don't read the prove ratio as "zippel
        /// circuit vs. native SNARK"; read it as "the comparison the
        /// user asked for".
        fn time_mvm(&self) -> Duration {
            use ark_ff::Zero;
            use ark_poly::EvaluationDomain;
            let mat = &self.translated.mat;
            let full = &self.translated.full_assignment;
            let num_inputs = self.translated.num_inputs;
            let num_constraints = self.translated.num_constraints;
            let zero = GitFr::zero();
            let domain_size = num_constraints + num_inputs;
            let domain_size = ark_poly::GeneralEvaluationDomain::<GitFr>::new(domain_size)
                .expect("domain")
                .size();
            let mut a = vec![zero; domain_size];
            let mut b = vec![zero; domain_size];
            let mut c = vec![zero; domain_size];
            let t = Instant::now();
            for (i, row) in mat.a.iter().enumerate() {
                for (cc, j) in row {
                    a[i] += *cc * full[*j];
                }
            }
            for (i, row) in mat.b.iter().enumerate() {
                for (cc, j) in row {
                    b[i] += *cc * full[*j];
                }
            }
            for (i, row) in mat.c.iter().enumerate() {
                for (cc, j) in row {
                    c[i] += *cc * full[*j];
                }
            }
            for i in 0..num_inputs {
                a[num_constraints + i] = full[i];
            }
            let elapsed = t.elapsed();
            std::hint::black_box((a, b, c));
            elapsed
        }

        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();
            let r = GitFr::rand(&mut rng);
            let s = GitFr::rand(&mut rng);

            let t = Instant::now();
            let proof = prove(
                &self.keys,
                &self.translated.mat,
                self.translated.num_inputs,
                self.translated.num_constraints,
                &self.translated.full_assignment,
                &self.translated.witness_assignment,
                self.translated.h_size,
                r,
                s,
            );
            let prove_t = t.elapsed();
            let mvm_t = self.time_mvm();
            let prove_adjusted = prove_t.saturating_sub(mvm_t);

            // Verifier convention: drop the leading constant-1 from the
            // public-input vector (matches ark-groth16's verify_proof).
            let public_inputs = &self.translated.instance_assignment[1..];
            let t = Instant::now();
            let ok = verify(&self.keys, &proof, public_inputs);
            let verify_t = t.elapsed();
            assert!(ok, "native (vendored) Groth16 verification FAILED");

            Timing {
                prove: prove_adjusted,
                verify: verify_t,
            }
        }
    }

    pub struct Proof {
        pub a: G1Projective,
        pub b: G2Projective,
        pub c: G1Projective,
    }

    /// Vendored Groth16 prover (Sect. 3.2 of the paper, libsnark
    /// reduction). Single MSM per key vector; uses
    /// `VariableBaseMSM::msm_bigint` from git-main `ark_ec`.
    #[allow(clippy::too_many_arguments)]
    pub fn prove(
        keys: &AffineKeys,
        mat: &super::bridge::GitMatrices,
        num_inputs: usize,
        num_constraints: usize,
        full_assignment: &[GitFr],
        witness_assignment: &[GitFr],
        h_size: usize,
        r: GitFr,
        s: GitFr,
    ) -> Proof {
        // h_coeffs (also folded into the timer on the zippel side).
        let mut h_coeffs = witness_map(mat, num_inputs, num_constraints, full_assignment);
        h_coeffs.resize(h_size, GitFr::zero_scalar());

        let full_bi: Vec<<GitFr as PrimeField>::BigInt> =
            full_assignment.iter().map(|x| x.into_bigint()).collect();
        let wit_bi: Vec<<GitFr as PrimeField>::BigInt> =
            witness_assignment.iter().map(|x| x.into_bigint()).collect();
        let h_bi: Vec<<GitFr as PrimeField>::BigInt> =
            h_coeffs.iter().map(|x| x.into_bigint()).collect();

        // A = alpha + MSM(a_query, full_assignment) + delta * r
        let a_msm = G1Projective::msm_bigint(&keys.a_query, &full_bi);
        let a = keys.alpha_g1.into_group() + a_msm + keys.delta_g1.into_group() * r;

        // B (G2) = beta + MSM(b_g2_query, full_assignment) + delta_g2 * s
        let b_g2_msm = G2Projective::msm_bigint(&keys.b_g2_query, &full_bi);
        let b_g2 = keys.beta_g2_aff.into_group() + b_g2_msm + keys.delta_g2_aff.into_group() * s;

        // B (G1) = beta_g1 + MSM(b_g1_query, full_assignment) + delta_g1 * s
        let b_g1_msm = G1Projective::msm_bigint(&keys.b_g1_query, &full_bi);
        let b_g1 = keys.beta_g1.into_group() + b_g1_msm + keys.delta_g1.into_group() * s;

        // C = MSM(l_query, witness) + MSM(h_query, h) + A·s + B₁·r − δ·r·s
        let l_msm = G1Projective::msm_bigint(&keys.l_query, &wit_bi);
        let h_msm = G1Projective::msm_bigint(&keys.h_query, &h_bi);
        let rs = r * s;
        let c = l_msm + h_msm + a * s + b_g1 * r - keys.delta_g1.into_group() * rs;

        Proof { a, b: b_g2, c }
    }

    /// Vendored Groth16 verifier. One MSM over `gamma_abc_g1` plus a
    /// single 3-pair `multi_pairing` (one Miller loop + one
    /// final-exponentiation), then GT identity check via `result == result − result`.
    pub fn verify(keys: &AffineKeys, proof: &Proof, public_inputs: &[GitFr]) -> bool {
        // IC = gamma_abc_g1[0] + MSM(gamma_abc_g1[1..], public_inputs).
        // public_inputs already drops the constant-1, matching the v0.5
        // ark-groth16 convention.
        let inputs_bi: Vec<<GitFr as PrimeField>::BigInt> =
            public_inputs.iter().map(|x| x.into_bigint()).collect();
        let ic_msm = G1Projective::msm_bigint(&keys.gamma_abc_g1[1..], &inputs_bi);
        let ic = keys.gamma_abc_g1[0].into_group() + ic_msm;

        // e(A, B) == e(α, β) · e(IC, γ) · e(C, δ)
        // ⟺ e(A, B) · e(−α, β) · e(−IC, γ) · e(−C, δ) == 1
        let a_aff = proof.a.into_affine();
        let b_aff = proof.b.into_affine();
        let neg_alpha = (-keys.alpha_g1.into_group()).into_affine();
        let neg_ic = (-ic).into_affine();
        let neg_c = (-proof.c).into_affine();

        let g1s = [a_aff, neg_alpha, neg_ic, neg_c];
        let g2s = [
            b_aff,
            keys.beta_g2_aff,
            keys.gamma_g2_aff,
            keys.delta_g2_aff,
        ];
        let pairing = <E as Pairing>::multi_pairing(g1s, g2s);
        // Identity check via the GT-equality trick used elsewhere in
        // benchmarks/: `result == result − result` (so we avoid an extra
        // pairing just to compute the identity).
        pairing == pairing - pairing
    }

    // Small helper: ark-ff git main exposes `GitFr::zero()` via the
    // `Zero` trait, but our own callers below only need a one-off
    // shortcut without dragging the trait import into the signature
    // line. Keep it inline as `zero_scalar()` for clarity.
    trait ZeroScalar {
        fn zero_scalar() -> Self;
    }
    impl ZeroScalar for GitFr {
        fn zero_scalar() -> Self {
            use ark_ff::Zero;
            <GitFr as Zero>::zero()
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level convenience: build a `Translated` from a `num_constraints`.
// `bench_all` and the standalone bin both go through this so the v0.5 →
// git-main translation cost happens once per size, not per side.
// ---------------------------------------------------------------------------

pub fn build_translated(num_constraints: usize) -> bridge::Translated {
    bridge::translate_shared(&shared::build(num_constraints))
}

// ---------------------------------------------------------------------------
// Cross-verification tests: confirm that zippel and native compute the same
// Groth16 protocol by having each side verify the other's proof. Unlike
// KZG, Groth16 is randomized (prover picks blinding factors r, s), so two
// runs with different randomness produce different valid proofs — we
// cannot assert byte-equality. We only assert mutual acceptance:
//
//   * Test 1: native produces a Proof; zippel verifier accepts it.
//   * Test 2: zippel produces a Proof; native verifier accepts it.
//
// If either test fails, the two sides are not implementing the same
// protocol and the benchmark comparison is invalid.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use super::bridge::{Translated, witness_map};
    use super::native_side::{AffineKeys, Proof, prove, verify};
    use super::{build_translated, zippel_side};
    use ark_bls12_381::Fr as GitFr;
    use ark_ff::{UniformRand, Zero};
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    /// Sweep used by both cross-tests. Capped at log_2 num_constraints = 6
    /// (= 64 constraints, M ≈ 65 inputs, L ≈ 128 witnesses) so each test
    /// stays under ~15 seconds. Larger sizes work but increase test wall-
    /// clock without exercising additional logic.
    const LOG_SWEEP: &[usize] = &[2, 4, 6];

    /// Build a zippel handler for Groth16, compiled at the given (M, L, H)
    /// sizes. The .zippel path is resolved relative to the benchmarks crate
    /// manifest so tests work regardless of cargo's cwd.
    fn zippel_handler(t: &Translated) -> ZippelHandler<ArkBls12_381> {
        let zippel_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("examples/groth16/groth16.zippel");
        let args = ZippelArgs::new(zippel_path);
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("M"), &t.m);
        sizes.insert(&Tid::new("L"), &t.l);
        sizes.insert(&Tid::new("H"), &t.h_size);
        handler.compile(&sizes);
        handler
    }

    /// Build the zippel-side input context from a `Translated`. Mirrors
    /// the construction in `zippel_side::Setup::new` but inlined so this
    /// test module doesn't reach into Setup's private fields.
    fn zip_inputs_from_translated(t: &Translated) -> Ctx<Vid, Value<ArkBls12_381>> {
        // h_coeffs is the QAP witness-map output, computed in Rust on the
        // zippel side too (since zippel can't express the QAP reduction
        // inside the proto). Match the zippel bench's behavior.
        let mut h_coeffs = witness_map(
            &t.mat,
            t.num_inputs,
            t.num_constraints,
            &t.full_assignment,
        );
        h_coeffs.resize(t.h_size, GitFr::zero());

        Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
            (Vid("alpha_g1".to_string()), Value::G1(t.keys.alpha_g1)),
            (Vid("beta_g2".to_string()), Value::G2(t.keys.beta_g2)),
            (Vid("gamma_g2".to_string()), Value::G2(t.keys.gamma_g2)),
            (Vid("delta_g2".to_string()), Value::G2(t.keys.delta_g2)),
            (
                Vid("gamma_abc_g1".to_string()),
                Value::VecG1(t.keys.gamma_abc_g1.clone()),
            ),
            (Vid("beta_g1".to_string()), Value::G1(t.keys.beta_g1)),
            (Vid("delta_g1".to_string()), Value::G1(t.keys.delta_g1)),
            (Vid("a_query".to_string()), Value::VecG1(t.keys.a_query.clone())),
            (
                Vid("b_g1_query".to_string()),
                Value::VecG1(t.keys.b_g1_query.clone()),
            ),
            (
                Vid("b_g2_query".to_string()),
                Value::VecG2(t.keys.b_g2_query.clone()),
            ),
            (Vid("h_query".to_string()), Value::VecG1(t.keys.h_query.clone())),
            (Vid("l_query".to_string()), Value::VecG1(t.keys.l_query.clone())),
            (
                Vid("instance_assignment".to_string()),
                Value::VecScalar(t.instance_assignment.clone()),
            ),
            (
                Vid("witness_assignment".to_string()),
                Value::VecScalar(t.witness_assignment.clone()),
            ),
            (Vid("h_coeffs".to_string()), Value::VecScalar(h_coeffs)),
        ])
    }

    /// Test 1: native produces (a, b, c); zippel verifier accepts it.
    #[test]
    fn native_prove_then_zippel_verify() {
        for &log_constraints in LOG_SWEEP {
            run_native_prove_zippel_verify(log_constraints);
        }
    }

    fn run_native_prove_zippel_verify(log_constraints: usize) {
        let num_constraints = 1usize << log_constraints;
        let t = build_translated(num_constraints);

        // ---- Native: build keys, sample randomness, produce Proof ---------
        let keys = AffineKeys::from(&t);
        let mut rng = ark_std::test_rng();
        let r = GitFr::rand(&mut rng);
        let s = GitFr::rand(&mut rng);
        let proof_n = prove(
            &keys,
            &t.mat,
            t.num_inputs,
            t.num_constraints,
            &t.full_assignment,
            &t.witness_assignment,
            t.h_size,
            r,
            s,
        );

        // Sanity: native's own verifier accepts native's proof (drop the
        // leading constant-1 from instance assignment, matching the
        // libsnark convention).
        let public_inputs = &t.instance_assignment[1..];
        assert!(
            verify(&keys, &proof_n, public_inputs),
            "log_constraints={log_constraints}: native verifier rejected its own proof — bug in this test"
        );

        // ---- Zippel: compile handler, prime state via run_prover, then
        //      run_verifier against the NATIVE-produced proof --------------
        let mut handler = zippel_handler(&t);
        let zip_inputs = zip_inputs_from_translated(&t);
        let prover_sched = handler.default_schedule_prover();
        let _ = handler
            .run_prover(prover_sched, zip_inputs)
            .expect("zippel run_prover (priming handler state)");

        // The zippel transcript is [a_proof, b_proof, c_proof] in `<-` order
        // (lines 38, 39, 44 of groth16.zippel).
        let cross_proof: Vec<Value<ArkBls12_381>> = vec![
            Value::G1(proof_n.a),
            Value::G2(proof_n.b),
            Value::G1(proof_n.c),
        ];
        let verifier_sched = handler.default_schedule_verifier();
        let verifier_result = handler
            .run_verifier(verifier_sched, cross_proof)
            .expect("zippel run_verifier on cross-proof");
        let result = check_verification(verifier_result);
        assert!(
            result.passed,
            "log_constraints={log_constraints}: CROSS-VERIFY FAILED: zippel verifier rejected native-produced proof"
        );
    }

    /// Test 2: zippel produces (a, b, c) via run_prover; native verifier
    /// accepts it.
    #[test]
    fn zippel_prove_then_native_verify() {
        for &log_constraints in LOG_SWEEP {
            run_zippel_prove_native_verify(log_constraints);
        }
    }

    fn run_zippel_prove_native_verify(log_constraints: usize) {
        let num_constraints = 1usize << log_constraints;
        let t = build_translated(num_constraints);

        // ---- Zippel: run_prover and extract (a, b, c) from the transcript -
        let mut handler = zippel_handler(&t);
        let zip_inputs = zip_inputs_from_translated(&t);
        let prover_sched = handler.default_schedule_prover();
        let zip_proof: Vec<Value<ArkBls12_381>> = handler
            .run_prover(prover_sched, zip_inputs)
            .expect("zippel run_prover");

        assert_eq!(
            zip_proof.len(),
            3,
            "log_constraints={log_constraints}: expected 3 transcript items (a, b, c)"
        );
        let a = match &zip_proof[0] {
            Value::G1(g) => *g,
            other => panic!(
                "expected G1 a_proof, got variant {:?}",
                std::mem::discriminant(other)
            ),
        };
        let b = match &zip_proof[1] {
            Value::G2(g) => *g,
            other => panic!(
                "expected G2 b_proof, got variant {:?}",
                std::mem::discriminant(other)
            ),
        };
        let c = match &zip_proof[2] {
            Value::G1(g) => *g,
            other => panic!(
                "expected G1 c_proof, got variant {:?}",
                std::mem::discriminant(other)
            ),
        };
        let proof_z = Proof { a, b, c };

        // ---- Native: verify the zippel-produced proof --------------------
        let keys = AffineKeys::from(&t);
        let public_inputs = &t.instance_assignment[1..];
        assert!(
            verify(&keys, &proof_z, public_inputs),
            "log_constraints={log_constraints}: CROSS-VERIFY FAILED: native verifier rejected zippel-produced proof"
        );
    }
}
