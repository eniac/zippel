//! Schnorr comparison: zippel-compiled Schnorr sigma protocol vs.
//! `ark-crypto-primitives::signature::schnorr` (the Fiat-Shamir
//! signature form).
//!
//! Statement on both sides: prover knows `x` such that `h = g·x` on the
//! BLS12-381 G1 group. Cost is dominated by 1 scalar mult on prove,
//! 1 two-base MSM on verify, plus a hash. The API surfaces differ
//! (interactive sigma vs. signature-on-message) but the core group
//! work is the same — fair for timing.
//!
//! Both sides use the same curve (BLS12-381 G1) so the comparison
//! isolates the protocol-layer overhead zippel adds on top of arkworks.

use crate::Timing;

pub mod zippel_side {
    use super::*;
    use ark_std::UniformRand;
    use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
    use lang::id::Vid;
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        compile_time: std::time::Duration,
    }

    impl Setup {
        pub fn new() -> Self {
            let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/schnorr/schnorr.zippel");
            let compile_start = Instant::now();
            let args = ZippelArgs::new(zippel_file);
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            handler.compile(&Ctx::new());
            let compile_time = compile_start.elapsed();
            Setup {
                handler,
                compile_time,
            }
        }

        pub fn compile_time(&self) -> std::time::Duration {
            self.compile_time
        }

        pub fn time_protocol(&mut self) -> Timing {
            type F = <ArkBls12_381 as ArkConfig>::F;
            type G1 = <ArkBls12_381 as ArkConfig>::G1;
            type G1Ops = <ArkBls12_381 as ArkConfig>::G1Ops;

            let mut rng = rand::rngs::OsRng;
            let x = F::rand(&mut rng);
            let g = G1::rand(&mut rng);
            let h_affines = G1Ops::vec_mul(&g, &vec![x]);
            let h = h_affines.into_iter().next().unwrap();
            let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("x".to_string()), Value::Scalar(x)),
                (Vid("g".to_string()), Value::G1(g)),
                (Vid("h".to_string()), Value::G1Affine(h)),
            ]);

            // Average the prover over VERIFY_SAMPLES samples too.
            // Schnorr's sign is ~0.1ms — single-shot is dominated by
            // jitter — so we sample at the same rate as the verifier.
            // Inputs + scheduled both have to be cloned per iter since
            // run_prover consumes them; clones happen outside the per-
            // call timer.
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let inputs_c = inputs.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(&inputs_c)
                    .expect("run_prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / crate::VERIFY_SAMPLES;
            let proof = last_proof.expect("VERIFY_SAMPLES > 0");
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(&proof_c)
                    .expect("run_verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;

            let result = check_verification(&last_result.expect("VERIFY_SAMPLES > 0"));
            assert!(result, "zippel schnorr verification FAILED");

            Timing { prove, verify }
        }
    }
}

pub mod native_side {
    use super::*;
    use blake2::Blake2s256;
    use ark_bls12_381::G1Projective;
    use ark_crypto_primitives::signature::{SignatureScheme, schnorr::Schnorr};
    use std::time::Instant;

    type SchnorrSig = Schnorr<G1Projective, Blake2s256>;

    pub struct Setup {
        params: <SchnorrSig as SignatureScheme>::Parameters,
        pk: <SchnorrSig as SignatureScheme>::PublicKey,
        sk: <SchnorrSig as SignatureScheme>::SecretKey,
        message: Vec<u8>,
    }

    impl Setup {
        pub fn new() -> Self {
            let mut rng = ark_std::test_rng();
            let params = SchnorrSig::setup(&mut rng).expect("schnorr setup");
            let (pk, sk) = SchnorrSig::keygen(&params, &mut rng).expect("schnorr keygen");
            Setup {
                params,
                pk,
                sk,
                message: b"benchmark message".to_vec(),
            }
        }

        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();

            // Average the prover over VERIFY_SAMPLES samples — schnorr's
            // sign is ~0.1ms so single-shot is jitter-dominated; we sample
            // at the same rate as the verifier for symmetry. Sign uses
            // fresh randomness per call (and so does the zippel side, via
            // `random<F>` in the proto), so each sample is an independent
            // signature; the last one is what we verify against.
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_sig = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let t = Instant::now();
                let sig = SchnorrSig::sign(&self.params, &self.sk, &self.message, &mut rng)
                    .expect("schnorr sign");
                prove_sum += t.elapsed();
                last_sig = Some(sig);
            }
            let prove = prove_sum / crate::VERIFY_SAMPLES;
            let sig = last_sig.expect("VERIFY_SAMPLES > 0");

            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_ok = false;
            for _ in 0..crate::VERIFY_SAMPLES {
                let t = Instant::now();
                let ok = SchnorrSig::verify(&self.params, &self.pk, &self.message, &sig)
                    .expect("schnorr verify");
                verify_sum += t.elapsed();
                last_ok = ok;
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;

            assert!(last_ok, "ark-crypto-primitives schnorr verification FAILED");

            Timing { prove, verify }
        }
    }
}
