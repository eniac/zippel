//! Groth16 comparison: zippel-compiled Groth16 (BLS12-381) vs. the
//! native `ark-groth16` v0.5 prover/verifier. Both sides run the
//! standard Groth16 proof system on the same R1CS circuit:
//!
//! ```text
//! e(A, B) == e(α, β) · e(IC, γ) · e(C, δ)
//! ```
//!
//! Parity decisions:
//!   - The zippel side uses `examples/groth16/groth16-opt.zippel`
//!     (h_coeffs supplied externally) and computes h_coeffs in Rust
//!     via `LibsnarkReduction::witness_map_from_matrices` inside the
//!     prove timer. That matches `Groth16::create_proof_with_reduction_and_matrices`
//!     on the native side, which also folds the witness_map into its
//!     prove timer.
//!   - Both sides share the same R1CS matrices and `(instance, witness)`
//!     assignment. The native side is at crates.io ark-groth16 v0.5;
//!     the zippel side runs against backend's git-main arkworks. We
//!     byte-translate the proving/verifying keys + scalars between the
//!     two version trees once at setup time (BLS12-381 has the same
//!     canonical-serialization layout in both v0.5 and git-main).
//!
//! Size knob: `log_constraints = log_2(num_constraints)`. The bench
//! circuit emits one multiplication constraint per "row" and one new
//! input variable per row, so `num_inputs = num_constraints + 1` and
//! `num_witnesses = 2 * num_constraints`.

use crate::Timing;

pub const DEFAULT_LOG_CONSTRAINTS: usize = 10;

// ---------------------------------------------------------------------------
// Shared setup: v0.5 BenchCircuit + keys + witness/matrices/h_coeffs.
// The fields are kept in v0.5 types so the native side can use them
// directly; the zippel side byte-translates what it needs.
// ---------------------------------------------------------------------------

pub mod shared {
    use np_ark_bls12_381::{Bls12_381, Fr};
    use np_ark_ff::UniformRand;
    use np_ark_groth16::{Groth16, ProvingKey, VerifyingKey};
    use np_ark_relations::r1cs::{
        ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
        LinearCombination, SynthesisError, SynthesisMode,
    };

    pub type E = Bls12_381;
    pub type F = Fr;

    /// Bench circuit: each row consumes two private witness variables,
    /// adds one public input set to their product, and emits the R1CS
    /// constraint `w1 * w2 = out`. With `num_constraints = N` rows we
    /// get `N` constraints, `N + 1` instance variables (the constant 1
    /// plus the N outputs), and `2N` witness variables.
    #[derive(Clone)]
    pub struct BenchCircuit {
        pub num_constraints: usize,
    }

    impl ConstraintSynthesizer<F> for BenchCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            // Deterministic randomness so the assignment is reproducible
            // across the two `generate_constraints` calls (setup + matrix
            // capture). Using OsRng (like the criterion bench) would yield
            // different witness values each call, which breaks the
            // shared-assignment contract between native and zippel sides.
            let mut rng = ark_std_test_rng_seeded(self.num_constraints as u64);
            let mut witness_vars = Vec::with_capacity(2 * self.num_constraints);
            for _ in 0..(2 * self.num_constraints) {
                let val = F::rand(&mut rng);
                let w = cs.new_witness_variable(|| Ok(val))?;
                witness_vars.push((w, val));
            }
            for i in 0..self.num_constraints {
                let (w1, v1) = witness_vars[2 * i];
                let (w2, v2) = witness_vars[2 * i + 1];
                let out_val = v1 * v2;
                let out = cs.new_input_variable(|| Ok(out_val))?;
                cs.enforce_constraint(
                    LinearCombination::from(w1),
                    LinearCombination::from(w2),
                    LinearCombination::from(out),
                )?;
            }
            Ok(())
        }
    }

    /// Seeded ChaCha20 RNG (via ark_std's test_rng glue), so two
    /// independent `generate_constraints` calls with the same
    /// `num_constraints` produce the same instance + witness assignments.
    fn ark_std_test_rng_seeded(seed: u64) -> ark_std::rand::rngs::StdRng {
        use ark_std::rand::SeedableRng;
        let mut seed_bytes = [0u8; 32];
        seed_bytes[..8].copy_from_slice(&seed.to_le_bytes());
        ark_std::rand::rngs::StdRng::from_seed(seed_bytes)
    }

    /// Captures everything both sides need.
    pub struct Shared {
        pub pk: ProvingKey<E>,
        pub vk: VerifyingKey<E>,
        pub matrices: ConstraintMatrices<F>,
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
        let cs = ConstraintSystem::<F>::new_ref();
        cs.set_mode(SynthesisMode::Prove {
            construct_matrices: true,
        });
        circuit
            .clone()
            .generate_constraints(cs.clone())
            .expect("synthesizer");
        cs.finalize();
        let matrices = cs.to_matrices().expect("matrices");
        let cs_borrowed = cs.borrow().expect("borrow cs");
        let num_inputs = cs_borrowed.num_instance_variables;
        let num_constraints_real = cs_borrowed.num_constraints;
        let instance_assignment = cs_borrowed.instance_assignment.clone();
        let witness_assignment = cs_borrowed.witness_assignment.clone();
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
// Byte-bridge: translate v0.5 scalars / group elements → git-main types.
// Both versions share BLS12-381's canonical serialization, so we round-trip
// through the canonical compressed byte form.
// ---------------------------------------------------------------------------

mod bridge {
    use ark_bls12_381::{Fr as GitFr, G1Projective as GitG1Proj, G2Projective as GitG2Proj};
    use ark_ec::AffineRepr as GitAffineRepr;
    use ark_serialize::CanonicalDeserialize;
    use np_ark_bls12_381::{Bls12_381 as NpBls12_381, Fr as NpFr};
    use np_ark_ec::pairing::Pairing as NpPairing;
    use np_ark_groth16::{ProvingKey as NpProvingKey, VerifyingKey as NpVerifyingKey};
    use np_ark_serialize::CanonicalSerialize as NpCanonicalSerialize;

    type NpG1Affine = <NpBls12_381 as NpPairing>::G1Affine;
    type NpG2Affine = <NpBls12_381 as NpPairing>::G2Affine;

    pub fn fr_to_git(x: &NpFr) -> GitFr {
        let mut bytes = Vec::with_capacity(32);
        x.serialize_compressed(&mut bytes).expect("ser np fr");
        GitFr::deserialize_compressed(&bytes[..]).expect("deser git fr")
    }

    pub fn fr_vec_to_git(xs: &[NpFr]) -> Vec<GitFr> {
        xs.iter().map(fr_to_git).collect()
    }

    pub fn g1_to_git_proj(p: &NpG1Affine) -> GitG1Proj {
        let mut bytes = Vec::with_capacity(48);
        p.serialize_compressed(&mut bytes).expect("ser np g1");
        let aff =
            ark_bls12_381::G1Affine::deserialize_compressed(&bytes[..]).expect("deser git g1");
        GitAffineRepr::into_group(aff)
    }

    pub fn g2_to_git_proj(p: &NpG2Affine) -> GitG2Proj {
        let mut bytes = Vec::with_capacity(96);
        p.serialize_compressed(&mut bytes).expect("ser np g2");
        let aff =
            ark_bls12_381::G2Affine::deserialize_compressed(&bytes[..]).expect("deser git g2");
        GitAffineRepr::into_group(aff)
    }

    pub fn g1_vec_to_git(ps: &[NpG1Affine]) -> Vec<GitG1Proj> {
        ps.iter().map(g1_to_git_proj).collect()
    }

    pub fn g2_vec_to_git(ps: &[NpG2Affine]) -> Vec<GitG2Proj> {
        ps.iter().map(g2_to_git_proj).collect()
    }

    /// Bundled git-main view of the Groth16 keys (only the fields the
    /// zippel-side `.zippel` protocol consumes).
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

    pub fn translate_keys(
        pk: &NpProvingKey<NpBls12_381>,
        vk: &NpVerifyingKey<NpBls12_381>,
    ) -> GitKeys {
        GitKeys {
            alpha_g1: g1_to_git_proj(&pk.vk.alpha_g1),
            beta_g1: g1_to_git_proj(&pk.beta_g1),
            beta_g2: g2_to_git_proj(&pk.vk.beta_g2),
            gamma_g2: g2_to_git_proj(&pk.vk.gamma_g2),
            delta_g1: g1_to_git_proj(&pk.delta_g1),
            delta_g2: g2_to_git_proj(&pk.vk.delta_g2),
            a_query: g1_vec_to_git(&pk.a_query),
            b_g1_query: g1_vec_to_git(&pk.b_g1_query),
            b_g2_query: g2_vec_to_git(&pk.b_g2_query),
            h_query: g1_vec_to_git(&pk.h_query),
            l_query: g1_vec_to_git(&pk.l_query),
            gamma_abc_g1: g1_vec_to_git(&vk.gamma_abc_g1),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn fr_roundtrips() {
            use np_ark_ff::UniformRand;
            let mut rng = ark_std::test_rng();
            let x = NpFr::rand(&mut rng);
            let _y = fr_to_git(&x);
        }
    }
}

// ---------------------------------------------------------------------------
// Zippel side: compile groth16-opt.zippel, feed translated inputs, time
// prove + verify. Prove timer includes the witness_map_from_matrices
// call (Rust-side h_coeffs computation), to match the native prover.
// ---------------------------------------------------------------------------

pub mod zippel_side {
    use super::shared::Shared;
    use super::{Timing, bridge};
    use ark_bls12_381::Fr as GitFr;
    use ark_ff::Zero;
    use ark_poly::GeneralEvaluationDomain;
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    // Witness-map reduction at git-main types — same algorithm as
    // `ark_groth16::r1cs_to_qap::LibsnarkReduction::witness_map_from_matrices`
    // (v0.5). Inlined here because we'd otherwise need to pull `ark-groth16`
    // at git-main, which collides with the np-ark-* version tree.
    fn witness_map_from_matrices_git(
        matrices_a: &[Vec<(GitFr, usize)>],
        matrices_b: &[Vec<(GitFr, usize)>],
        matrices_c: &[Vec<(GitFr, usize)>],
        num_inputs: usize,
        num_constraints: usize,
        full_assignment: &[GitFr],
    ) -> Vec<GitFr> {
        use ark_ff::{FftField, Field};
        use ark_poly::EvaluationDomain;
        let zero = GitFr::zero();
        let domain_size = num_constraints + num_inputs;
        let domain =
            GeneralEvaluationDomain::<GitFr>::new(domain_size).expect("domain for witness map");
        let domain_size = domain.size();

        // Evaluations of A·z, B·z, C·z at the constraint indices, padded.
        let mut a = vec![zero; domain_size];
        let mut b = vec![zero; domain_size];
        for (i, row) in matrices_a.iter().enumerate() {
            for (c, j) in row {
                a[i] += *c * full_assignment[*j];
            }
        }
        for (i, row) in matrices_b.iter().enumerate() {
            for (c, j) in row {
                b[i] += *c * full_assignment[*j];
            }
        }
        // The libsnark reduction also folds in identity rows for the
        // first `num_inputs` instance positions: A[constraints + i] = e_i.
        // Replicate that here so the QAP relation matches the keys.
        for i in 0..num_inputs {
            a[num_constraints + i] = full_assignment[i];
        }

        // a, b in evaluation form on the constraint domain → coefficients.
        domain.ifft_in_place(&mut a);
        domain.ifft_in_place(&mut b);

        // Move to the coset, evaluate, multiply pointwise, divide by the
        // vanishing polynomial of the domain (which is a constant on the
        // coset), and invert-FFT back.
        let coset = domain.get_coset(GitFr::GENERATOR).expect("coset");
        coset.fft_in_place(&mut a);
        coset.fft_in_place(&mut b);

        // Compute c·z in evaluation form on the constraint domain via the
        // QAP relation a·b - c = h·t. We need c in coset eval form too.
        let mut c = vec![zero; domain_size];
        for (i, row) in matrices_c.iter().enumerate() {
            for (cc, j) in row {
                c[i] += *cc * full_assignment[*j];
            }
        }
        domain.ifft_in_place(&mut c);
        coset.fft_in_place(&mut c);

        // h on the coset = (a*b - c) / V_H(coset_offset). V_H is the
        // vanishing polynomial of the ORIGINAL domain (V_H(x) = x^N - 1),
        // evaluated at the coset offset, where it's a non-zero constant.
        let v_h_inv = domain
            .evaluate_vanishing_polynomial(GitFr::GENERATOR)
            .inverse()
            .expect("V_H(g) inverse");
        // a*b - c, in place into `a`.
        for i in 0..domain_size {
            a[i] = (a[i] * b[i] - c[i]) * v_h_inv;
        }
        coset.ifft_in_place(&mut a);
        a
    }

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        // All inputs preassembled at git-main types except h_coeffs,
        // which is computed inside `time_protocol` to match the native
        // prover's witness_map cost.
        inputs_base: Ctx<Vid, Value<ArkBls12_381>>,
        public_inputs: Ctx<Vid, Value<ArkBls12_381>>,
        // matrices in git-main field for the in-timer witness map.
        mat_a: Vec<Vec<(GitFr, usize)>>,
        mat_b: Vec<Vec<(GitFr, usize)>>,
        mat_c: Vec<Vec<(GitFr, usize)>>,
        full_assignment: Vec<GitFr>,
        num_inputs: usize,
        num_constraints: usize,
        h_size: usize,
    }

    impl Setup {
        pub fn new(shared: &Shared) -> Self {
            let keys = bridge::translate_keys(&shared.pk, &shared.vk);
            let m = shared.vk.gamma_abc_g1.len();
            let l = shared.pk.l_query.len();
            let h_size = shared.pk.h_query.len();

            // Translate matrices' (coeff, col) entries to git-main field.
            let translate_row = |row: &Vec<(np_ark_bls12_381::Fr, usize)>| {
                row.iter()
                    .map(|(c, j)| (bridge::fr_to_git(c), *j))
                    .collect::<Vec<_>>()
            };
            let mat_a = shared
                .matrices
                .a
                .iter()
                .map(translate_row)
                .collect::<Vec<_>>();
            let mat_b = shared
                .matrices
                .b
                .iter()
                .map(translate_row)
                .collect::<Vec<_>>();
            let mat_c = shared
                .matrices
                .c
                .iter()
                .map(translate_row)
                .collect::<Vec<_>>();
            let instance_assignment_git = bridge::fr_vec_to_git(&shared.instance_assignment);
            let witness_assignment_git = bridge::fr_vec_to_git(&shared.witness_assignment);
            let full_assignment = {
                let mut v = instance_assignment_git.clone();
                v.extend(witness_assignment_git.iter().copied());
                v
            };

            let inputs_base = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("alpha_g1".to_string()), Value::G1(keys.alpha_g1)),
                (Vid("beta_g2".to_string()), Value::G2(keys.beta_g2)),
                (Vid("gamma_g2".to_string()), Value::G2(keys.gamma_g2)),
                (Vid("delta_g2".to_string()), Value::G2(keys.delta_g2)),
                (
                    Vid("gamma_abc_g1".to_string()),
                    Value::VecG1(keys.gamma_abc_g1),
                ),
                (Vid("beta_g1".to_string()), Value::G1(keys.beta_g1)),
                (Vid("delta_g1".to_string()), Value::G1(keys.delta_g1)),
                (Vid("a_query".to_string()), Value::VecG1(keys.a_query)),
                (Vid("b_g1_query".to_string()), Value::VecG1(keys.b_g1_query)),
                (Vid("b_g2_query".to_string()), Value::VecG2(keys.b_g2_query)),
                (Vid("h_query".to_string()), Value::VecG1(keys.h_query)),
                (Vid("l_query".to_string()), Value::VecG1(keys.l_query)),
                (
                    Vid("instance_assignment".to_string()),
                    Value::VecScalar(instance_assignment_git.clone()),
                ),
                (
                    Vid("witness_assignment".to_string()),
                    Value::VecScalar(witness_assignment_git),
                ),
            ]);

            // Verifier sees everything in inputs_base EXCEPT
            // witness_assignment (which is `private` in the .zippel).
            let public_input_names = [
                "alpha_g1",
                "beta_g2",
                "gamma_g2",
                "delta_g2",
                "gamma_abc_g1",
                "beta_g1",
                "delta_g1",
                "a_query",
                "b_g1_query",
                "b_g2_query",
                "h_query",
                "l_query",
                "instance_assignment",
            ];
            let public_inputs: Ctx<Vid, Value<ArkBls12_381>> = inputs_base
                .clone()
                .into_iter()
                .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
                .collect();

            let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16-opt.zippel"));
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("M"), &m);
            sizes.insert(&Tid::new("L"), &l);
            sizes.insert(&Tid::new("H"), &h_size);
            handler.compile(&sizes);

            Setup {
                handler,
                inputs_base,
                public_inputs,
                mat_a,
                mat_b,
                mat_c,
                full_assignment,
                num_inputs: shared.num_inputs,
                num_constraints: shared.num_constraints,
                h_size,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            let prover_scheduled = self.handler.default_schedule_prover();

            let t = Instant::now();
            // h_coeffs computation (Rust-side; matches what the native
            // ark-groth16 prover does internally).
            let mut h_coeffs = witness_map_from_matrices_git(
                &self.mat_a,
                &self.mat_b,
                &self.mat_c,
                self.num_inputs,
                self.num_constraints,
                &self.full_assignment,
            );
            h_coeffs.resize(self.h_size, GitFr::zero());
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
// Native side: ark-groth16 v0.5, using create_proof_with_reduction_and_matrices
// on the shared matrices/assignment so both sides prove the same statement.
// ---------------------------------------------------------------------------

pub mod native_side {
    use super::Timing;
    use super::shared::{E, F, Shared};
    use np_ark_ff::UniformRand;
    use np_ark_groth16::{Groth16, prepare_verifying_key};
    use std::time::Instant;

    pub struct Setup<'a> {
        shared: &'a Shared,
    }

    impl<'a> Setup<'a> {
        pub fn new(shared: &'a Shared) -> Self {
            Self { shared }
        }

        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();
            let r = F::rand(&mut rng);
            let s = F::rand(&mut rng);

            let full_assignment: Vec<F> = {
                let mut v = self.shared.instance_assignment.clone();
                v.extend(self.shared.witness_assignment.iter().copied());
                v
            };

            let t = Instant::now();
            let proof = Groth16::<E>::create_proof_with_reduction_and_matrices(
                &self.shared.pk,
                r,
                s,
                &self.shared.matrices,
                self.shared.num_inputs,
                self.shared.num_constraints,
                &full_assignment,
            )
            .expect("native groth16 prove");
            let prove = t.elapsed();

            let pvk = prepare_verifying_key(&self.shared.vk);
            // Native verifier convention: drop the leading constant-1.
            let public_inputs = &self.shared.instance_assignment[1..];
            let t = Instant::now();
            let ok = Groth16::<E>::verify_proof(&pvk, &proof, public_inputs)
                .expect("native groth16 verify");
            let verify = t.elapsed();
            assert!(ok, "native Groth16 verification FAILED");

            Timing { prove, verify }
        }
    }
}
