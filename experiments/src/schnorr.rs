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

/// Zippel half: compiles `examples/schnorr/schnorr.zippel` and times its
/// generated prover and verifier.
pub mod zippel_side {
    use super::*;
    use ark_std::UniformRand;
    use backend::{ArkBls12_381, Backend, Value};
    use lang::id::Vid;
    use share::Ctx;
    use std::path::PathBuf;
    use zippel::{
        CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    };

    /// The compiled Schnorr protocol. It takes no size parameters, so the only
    /// per-instance state is the projected roles and the measured compile time.
    pub struct Setup {
        prover: CompiledProver<ArkBls12_381>,
        verifier: CompiledVerifier<ArkBls12_381>,
        compile_time: Vec<std::time::Duration>,
    }

    impl Setup {
        /// Compiles `examples/schnorr/schnorr.zippel` with an empty size
        /// context and records how long the compile took.
        ///
        /// # Panics
        /// Panics if the `.zippel` source cannot be read, parsed, type
        /// checked, or lowered to prover and verifier graphs.
        pub fn new() -> Self {
            let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/schnorr/schnorr.zippel");
            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(&zippel_file).expect("parse protocol");
                let protocol: CompiledProtocol<ArkBls12_381> = module
                    .compile(&Ctx::new(), CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });
            Setup {
                prover,
                verifier,
                compile_time,
            }
        }

        /// Wall-time spent parsing, type checking, and building the prover and
        /// verifier graphs.
        pub fn compile_time(&self) -> Vec<std::time::Duration> {
            self.compile_time.clone()
        }

        /// (prover graph node count, verifier graph node count).
        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.prover.graph().node_count(),
                self.verifier.graph().node_count(),
            )
        }

        /// Samples a witness `x` and bases `g`, `h = g*x`, then times the
        /// compiled prover and verifier.
        ///
        /// # Panics
        /// Panics if the prover or verifier graph fails to execute, or if the
        /// verifier rejects the honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            type F = <ArkBls12_381 as Backend>::F;
            type G1 = <ArkBls12_381 as Backend>::G1;

            let mut rng = rand::rngs::OsRng;
            let x = F::rand(&mut rng);
            let g = G1::rand(&mut rng);
            let h_affines = backend::Group::batch_mul(&g, &[x]);
            let h = h_affines.into_iter().next().unwrap();
            let inputs = crate::harness_inputs([
                (Vid("x".to_string()), Value::Scalar(x)),
                (Vid("g".to_string()), Value::g1(g)),
                (Vid("h".to_string()), Value::g1_affine(h)),
            ]);

            let (prove, prove_peak, proof) = crate::sample_zippel_prover(&self.prover, &inputs);
            let (verify, verify_peak, passed) =
                crate::sample_zippel_verifier(&self.verifier, &proof, &inputs);
            assert!(passed, "zippel schnorr verification FAILED");

            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }

    impl Default for Setup {
        fn default() -> Self {
            Self::new()
        }
    }
}

/// Native baseline: `ark_crypto_primitives::signature::schnorr` in its
/// Fiat-Shamir signature form, over BLS12-381 G1 with a `Blake2s256` hash.
///
/// The API shape differs (sign/verify a message rather than an interactive
/// sigma protocol) but the group work — one scalar multiplication to prove,
/// one two-base MSM to verify — matches the zippel side.
pub mod native_side {
    use super::*;
    use ark_bls12_381::G1Projective;
    use ark_crypto_primitives::signature::{SignatureScheme, schnorr::Schnorr};
    use blake2::Blake2s256;

    type SchnorrSig = Schnorr<G1Projective, Blake2s256>;

    /// Signature-scheme parameters, key pair, and the fixed message that
    /// `time_protocol` signs and verifies.
    pub struct Setup {
        params: <SchnorrSig as SignatureScheme>::Parameters,
        pk: <SchnorrSig as SignatureScheme>::PublicKey,
        sk: <SchnorrSig as SignatureScheme>::SecretKey,
        message: Vec<u8>,
    }

    impl Setup {
        /// Runs the scheme's setup and key generation with a deterministic
        /// test RNG and fixes the benchmark message.
        ///
        /// # Panics
        /// Panics if setup or key generation fails.
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

        /// Times `sign` as the prover and `verify` as the verifier,
        /// [`crate::SAMPLES`] runs each.
        ///
        /// Each signature uses fresh randomness, mirroring the `random<F>`
        /// nonce on the zippel side; the last one is what gets verified.
        ///
        /// # Panics
        /// Panics if signing or verification errors out, or if the final
        /// signature fails to verify.
        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();

            // Sign uses fresh randomness per call (and so does the zippel side, via
            // `random<F>` in the proto), so each sample is an independent
            // signature; the last one is what we verify against.
            let (prove, prove_peak, sig) = crate::sample(|| {
                SchnorrSig::sign(&self.params, &self.sk, &self.message, &mut rng)
                    .expect("schnorr sign")
            });
            let (verify, verify_peak, passed) = crate::sample(|| {
                SchnorrSig::verify(&self.params, &self.pk, &self.message, &sig)
                    .expect("schnorr verify")
            });
            assert!(passed, "ark-crypto-primitives schnorr verification FAILED");

            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }

    impl Default for Setup {
        fn default() -> Self {
            Self::new()
        }
    }
}

// ---------------------------------------------------------------------------
// Cross-verification: each verifier accepts the other's proof. The native
// challenge is the signature hash, so Zippel draws it through `SignatureHash`.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use crate::cross::Direction;
    use ark_bls12_381::{Fr, G1Affine, G1Projective};
    use ark_crypto_primitives::signature::SignatureScheme;
    use ark_crypto_primitives::signature::schnorr::{Parameters, Schnorr, Signature};
    use ark_ec::CurveGroup;
    use ark_ff::Field;
    use ark_serialize::CanonicalSerialize;
    use backend::{ArkBls12_381, Value};
    use blake2::{Blake2s256, Digest};
    use zippel::runtime::Challenger;

    type SchnorrSig = Schnorr<G1Projective, Blake2s256>;
    type V = Value<ArkBls12_381>;

    const MESSAGE: &[u8] = b"cross-verification";

    fn g1(v: &V) -> G1Affine {
        match v {
            Value::G1(g) => g.into_affine(),
            Value::G1Affine(g) => **g,
            _ => panic!("expected G1, got {v}"),
        }
    }
    fn scalar(v: &V) -> Fr {
        match v {
            Value::Scalar(f) => *f,
            _ => panic!("expected a scalar, got {v}"),
        }
    }

    /// The native's challenge `e = H(salt ‖ u ‖ message)`, drawn as Zippel's
    /// `c = -e`: the native responds `s = r - x·e`, Zippel `z = r + x·c`. A hash
    /// that is no field element makes the native signer retry with a fresh nonce;
    /// `valid` says whether this one was.
    struct SignatureHash<'a> {
        params: &'a Parameters<G1Projective, Blake2s256>,
        u: Option<G1Affine>,
        valid: bool,
    }

    impl Challenger<ArkBls12_381> for SignatureHash<'_> {
        fn instance(&mut self, _: &V) {}

        fn message(&mut self, value: &V) {
            self.u = Some(g1(value));
        }

        fn challenge(&mut self) -> V {
            let mut input = Vec::new();
            self.params.salt.serialize_compressed(&mut input).unwrap();
            self.u.expect("u").serialize_compressed(&mut input).unwrap();
            MESSAGE.serialize_compressed(&mut input).unwrap();
            let e = Fr::from_random_bytes(&Blake2s256::digest(&input));
            self.valid = e.is_some();
            Value::Scalar(-e.unwrap_or_default())
        }
    }

    #[test]
    fn native_prove_then_zippel_verify() {
        cross_verify(Direction::NativeToZippel);
    }

    #[test]
    fn zippel_prove_then_native_verify() {
        cross_verify(Direction::ZippelToNative);
    }

    fn cross_verify(direction: Direction) {
        let mut rng = ark_std::test_rng();
        let params = SchnorrSig::setup(&mut rng).unwrap();
        let (pk, sk) = SchnorrSig::keygen(&params, &mut rng).unwrap();
        let (prover, verifier) = crate::cross::compile::<ArkBls12_381>("schnorr", &[]);
        let inputs = crate::harness_inputs([
            ("x", Value::Scalar(sk.0)),
            ("g", Value::g1_affine(params.generator)),
            ("h", Value::g1_affine(pk)),
        ]);
        let hash = || SignatureHash {
            params: &params,
            u: None,
            valid: false,
        };

        for _ in 0..8 {
            match direction {
                Direction::NativeToZippel => {
                    let sig = SchnorrSig::sign(&params, &sk, MESSAGE, &mut rng).unwrap();
                    let (s, e) = (sig.prover_response, sig.verifier_challenge);
                    let u = params.generator * s + pk * e;
                    assert!(
                        verifier
                            .verify_with(
                                vec![Value::g1(u), Value::Scalar(s)],
                                crate::lend(&inputs),
                                &mut hash()
                            )
                            .unwrap(),
                        "Zippel rejects the native signature"
                    );
                    assert!(
                        !verifier
                            .verify_with(
                                vec![Value::g1(u), Value::Scalar(s + Fr::ONE)],
                                crate::lend(&inputs),
                                &mut hash()
                            )
                            .unwrap(),
                        "Zippel accepts a wrong response"
                    );
                }
                Direction::ZippelToNative => {
                    let (proof, c) = loop {
                        let mut h = hash();
                        let proof = prover.prove_with(crate::lend(&inputs), &mut h).unwrap();
                        if h.valid {
                            let c = scalar(&h.challenge());
                            break (proof, c);
                        }
                    };
                    let sig = Signature {
                        prover_response: scalar(&proof[1]),
                        verifier_challenge: -c,
                    };
                    assert!(
                        SchnorrSig::verify(&params, &pk, MESSAGE, &sig).unwrap(),
                        "the native verifier rejects Zippel's proof"
                    );
                }
            }
        }
    }
}
