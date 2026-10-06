//! DeKART range-proof comparison: zippel-compiled `examples/dekart/dekart.zippel`
//! vs. the Aptos univariate DeKART v2 prover/verifier (vendored + ported to
//! arkworks 0.6 in `src/dekart_upstream/`), both on BLS12-381.
//!
//! Statement on both sides: n values z_1..z_n, each in [0, 2^ell), under a
//! hiding KZG commitment to f with f(ω^0) = 0, f(ω^i) = z_i on a domain of
//! size n+1. Radix b = 2 (the native implementation is binary-only).
//!
//! Both sides run the same protocol (Aptos' dekart_univariate_v2): same
//! statement, prover messages, challenges and challenge order, and verifier
//! checks. The proto follows upstream's step numbering.
//!
//! Parity decisions:
//!   - Same trapdoor (τ, ξ), same generators, same values, and the same
//!     statement (com_f, ρ) on both sides, built once in `shared`.
//!   - com_f is the public statement on both sides, so neither "prove" timer
//!     includes committing to f (as in upstream's own range_proof bench).
//!     Native "prove" includes the projective→affine proof normalisation.
//!   - Remaining Fiat–Shamir instantiation differences (no effect on the
//!     protocol's messages or cost): native hashes with merlin and draws
//!     128-bit β/μ; zippel uses its own transcript and full-width challenges.
//!   - n = 2^L − 1 so the domain (n+1) is a power of two, as upstream
//!     requires. `log_size` = L.
//!   - Both provers commit to the digit polynomials from their 0/1
//!     evaluations in the Lagrange basis (arkworks' small-scalar MSM path)
//!     and derive Ĉ from com_f. They differ in how h is computed: native
//!     works in evaluation form via the derivative trick; the zippel proto
//!     works on coefficient-form polynomials: interpolate (IFFT), multiply
//!     f_j·(f_j − 1) and divide once by V*(X) = 1 + X + … + X^n. Both are
//!     O(ell · n log n).

use crate::Timing;

pub const DEFAULT_LOG_N: usize = 8;
pub const DEFAULT_ELL: usize = 16;

pub mod shared {
    use ark_bls12_381::{Fr, G1Affine, G1Projective};
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, scalar_mul::ScalarMul};
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::rand::{RngCore, SeedableRng, rngs::StdRng};

    /// Per-size setup shared by both sides. Cached on disk keyed by
    /// log_size (independent of ell).
    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    pub struct Srs {
        pub tau: Fr,
        pub xi: Fr,
        /// [τ^i]_1 for i in 0..=n — zippel's `srs_g1_h`.
        pub powers_g1: Vec<G1Affine>,
        /// [ℓ_i(τ)]_1 over the size-(n+1) domain — native's `ck_s.lagr_g1`,
        /// zippel's `srs_g1_lagr`.
        pub lagr_g1: Vec<G1Affine>,
    }

    pub struct Shared {
        pub n: usize,
        pub ell: usize,
        pub srs: Srs,
        /// n values, each < 2^ell.
        pub values: Vec<u64>,
        /// Statement: com_f = Σ_i z_i·[ℓ_i(τ)]_1 + ρ·[ξ]_1 (with f(ω^0) = 0).
        pub rho: Fr,
        pub com_f: G1Affine,
    }

    /// # Panics
    /// Panics unless `log_n >= 1` and `1 <= ell <= 64`, or if the SRS
    /// artifact cannot be read or written.
    pub fn build(log_n: usize, ell: usize) -> Shared {
        assert!(log_n >= 1 && (1..=64).contains(&ell));
        let num_omegas = 1usize << log_n;
        let n = num_omegas - 1;
        let srs = crate::cache::load_or_build_canonical("dekart_srs", log_n, || {
            let mut rng = StdRng::seed_from_u64(0xDEC0);
            let tau: Fr = crate::dekart_upstream::sample_field_element(&mut rng);
            let xi: Fr = crate::dekart_upstream::sample_field_element(&mut rng);
            let g1 = G1Projective::from(G1Affine::generator());
            let mut pows = Vec::with_capacity(num_omegas);
            let mut acc = Fr::from(1u64);
            for _ in 0..num_omegas {
                pows.push(acc);
                acc *= tau;
            }
            let powers_g1 = g1.batch_mul(&pows);
            let dom = Radix2EvaluationDomain::<Fr>::new(num_omegas).unwrap();
            let lagr_g1 =
                crate::dekart_upstream::lagrange_basis::<G1Projective>(g1, tau, num_omegas, dom);
            // Σ_i ℓ_i(τ) = 1, so the Lagrange basis must sum to [1]_1.
            debug_assert_eq!(
                lagr_g1
                    .iter()
                    .map(|p| p.into_group())
                    .sum::<G1Projective>()
                    .into_affine(),
                powers_g1[0]
            );
            Srs {
                tau,
                xi,
                powers_g1,
                lagr_g1,
            }
        });
        // upstream `range_proof_random_instance`: rng.next_u64() >> (64 - ell)
        let mut rng = StdRng::seed_from_u64(42);
        let values: Vec<u64> = (0..n)
            .map(|_| {
                if ell == 64 {
                    rng.next_u64()
                } else {
                    rng.next_u64() >> (64 - ell)
                }
            })
            .collect();
        let rho: Fr = crate::dekart_upstream::sample_field_element(&mut rng);
        let scalars: Vec<Fr> = values.iter().map(|&z| Fr::from(z)).collect();
        let xi_1 = G1Projective::from(G1Affine::generator()) * srs.xi;
        let com_f =
            (G1Projective::msm(&srs.lagr_g1[1..], &scalars).unwrap() + xi_1 * rho).into_affine();
        Shared {
            n,
            ell,
            srs,
            values,
            rho,
            com_f,
        }
    }
}

pub mod zippel_side {
    use super::*;
    use ark_bls12_381::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
    use ark_ec::AffineRepr;
    use ark_ff::{One, Zero};
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{Inputs, ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        inputs: Inputs<ArkBls12_381>,
        compile_time: Vec<std::time::Duration>,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            Self::new_with_proto(sh, PathBuf::from("examples/dekart/dekart.zippel"))
        }

        /// Same inputs, different proto source (used by the `dekart_profile`
        /// bin to time truncated copies of the proto).
        pub fn new_with_proto(sh: &shared::Shared, proto: PathBuf) -> Self {
            let (n, ell) = (sh.n, sh.ell);
            let b = 2usize;
            let h_deg = (b - 1) * n;

            let (handler, compile_time) = crate::sample_compile(|| {
                let mut handler: ZippelHandler<ArkBls12_381> =
                    ZippelHandler::new(ZippelArgs::new(proto.clone()));
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("n"), &n);
                sizes.insert(&Tid::new("b"), &b);
                sizes.insert(&Tid::new("l_chunk"), &ell);
                handler.compile(&sizes);
                handler
            });

            let g1 = G1Projective::from(G1Affine::generator());
            let g2 = G2Projective::from(G2Affine::generator());
            let (tau, xi) = (sh.srs.tau, sh.srs.xi);

            let mut f_evals = vec![Fr::zero()];
            f_evals.extend(sh.values.iter().map(|&z| Fr::from(z)));
            let chunks_bits = (0..ell)
                .map(|j| {
                    Value::vec_scalar(sh.values.iter().map(|&z| Fr::from((z >> j) & 1)).collect())
                })
                .collect();
            let b_pow = (0..ell).map(|j| Fr::from(1u64 << j)).collect::<Vec<_>>();

            let inputs = Inputs::from_iter(
                [
                    // witness
                    ("f_evals", Value::vec_scalar(f_evals)),
                    ("chunks_bits", Value::Vec(chunks_bits)),
                    ("rho", Value::Scalar(sh.rho)),
                    // statement + public parameters
                    ("com_f", Value::G1(sh.com_f.into_group())),
                    ("b_pow", Value::vec_scalar(b_pow)),
                    ("gen_g1", Value::G1(g1)),
                    ("gen_g2", Value::G2(g2)),
                    ("srs_g2_tau", Value::G2(g2 * tau)),
                    ("srs_g2_xi", Value::G2(g2 * xi)),
                    ("xi_g1", Value::G1(g1 * xi)),
                    // s0 = Lagrange poly with s0(ω^0)=1, zero elsewhere on the domain.
                    ("s0_commit", Value::G1(sh.srs.lagr_g1[0].into_group())),
                    ("srs_g1_lagr", Value::vec_g1_affine(sh.srs.lagr_g1.clone())),
                    (
                        "srs_g1_h",
                        Value::vec_g1_affine(sh.srs.powers_g1[..=h_deg].to_vec()),
                    ),
                    ("v_star", Value::vec_scalar(vec![Fr::one(); n + 1])),
                ]
                .into_iter()
                .map(|(k, v)| (Vid(k.to_string()), v)),
            );

            Setup {
                handler,
                inputs,
                compile_time,
            }
        }

        /// Wall-time spent compiling the `.zippel` source into prover and
        /// verifier graphs. Excludes SRS construction and cache I/O.
        pub fn compile_time(&self) -> Vec<std::time::Duration> {
            self.compile_time.clone()
        }

        /// (prover graph node count, verifier graph node count).
        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.handler.prover_graph().node_count(),
                self.handler.verifier_graph().node_count(),
            )
        }

        /// Mean prover wall-clock over `samples` runs; no verification.
        pub fn time_prover_only(&mut self, samples: u32) -> std::time::Duration {
            let mut sum = std::time::Duration::ZERO;
            for _ in 0..samples {
                let t = Instant::now();
                self.handler
                    .run_prover(&self.inputs)
                    .expect("run_prover failed");
                sum += t.elapsed();
            }
            sum / samples
        }

        /// # Panics
        /// Panics if the prover or verifier graph fails to execute, or if the
        /// verifier rejects the honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            let (prove, prove_peak, proof) = crate::sample(|| {
                self.handler
                    .run_prover(&self.inputs)
                    .expect("run_prover failed")
            });
            let (verify, verify_peak, result) = crate::sample(|| {
                self.handler
                    .run_verifier(&proof, &self.inputs)
                    .expect("run_verifier failed")
            });
            assert!(
                check_verification(&result),
                "zippel DeKART verification FAILED"
            );
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}

pub mod native_side {
    use super::*;
    use crate::dekart_upstream::{self as dk, Proof, ProverKey, VerificationKey};
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ec::CurveGroup;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    pub struct Setup {
        pk: ProverKey<Bls12_381>,
        vk: VerificationKey<Bls12_381>,
        values: Vec<Fr>,
        rho: Fr,
        com_f: ark_bls12_381::G1Affine,
        n: usize,
        ell: usize,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            let (pk, vk) = dk::setup_for_testing::<Bls12_381>(
                sh.n,
                sh.ell,
                sh.srs.xi,
                sh.srs.tau,
                Some(sh.srs.lagr_g1.clone()),
            );
            let values = sh.values.iter().map(|&z| Fr::from(z)).collect();
            Setup {
                pk,
                vk,
                values,
                rho: sh.rho,
                com_f: sh.com_f,
                n: sh.n,
                ell: sh.ell,
            }
        }

        /// # Panics
        /// Panics if the native verifier rejects the honestly generated proof.
        pub fn time_protocol(&self) -> Timing {
            let mut rng = StdRng::seed_from_u64(7);
            let comm = self.com_f;
            debug_assert_eq!(
                dk::commit_with_randomness(&self.pk.ck_s, &self.values, self.rho).into_affine(),
                comm
            );

            let (prove, prove_peak, proof) = crate::sample(|| {
                let proof: Proof<Bls12_381> =
                    dk::prove(&self.pk, &self.values, self.ell, &comm, self.rho, &mut rng).into();
                proof
            });
            let (verify, verify_peak, ok) =
                crate::sample(|| proof.verify(&self.vk, self.n, self.ell, &comm));
            ok.expect("native DeKART verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}
