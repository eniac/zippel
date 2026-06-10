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
    }

    impl Setup {
        pub fn new() -> Self {
            let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/schnorr/schnorr.zippel");
            let args = ZippelArgs::new(zippel_file);
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            handler.compile(&Ctx::new());
            Setup { handler }
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

            let prover_scheduled = self.handler.default_schedule_prover();
            let t = Instant::now();
            let proof = self
                .handler
                .run_prover(prover_scheduled, inputs)
                .expect("run_prover failed");
            let prove = t.elapsed();

            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("run_verifier failed");
            let verify = t.elapsed();

            let result = check_verification(verifier_result);
            assert!(result.passed, "zippel schnorr verification FAILED");

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

            let t = Instant::now();
            let sig = SchnorrSig::sign(&self.params, &self.sk, &self.message, &mut rng)
                .expect("schnorr sign");
            let prove = t.elapsed();

            let t = Instant::now();
            let ok = SchnorrSig::verify(&self.params, &self.pk, &self.message, &sig)
                .expect("schnorr verify");
            let verify = t.elapsed();

            assert!(ok, "ark-crypto-primitives schnorr verification FAILED");

            Timing { prove, verify }
        }
    }
}
