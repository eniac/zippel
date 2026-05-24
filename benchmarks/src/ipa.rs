//! IPA comparison: zippel-compiled Bulletproofs inner-product argument
//! vs. `ark-poly-commit::ipa_pc::InnerProductArgPC` — both on Secp256k1.
//!
//! Same curve, so the comparison isolates protocol-layer overhead.
//! The two protocols are slightly different in flavor:
//!   - zippel proves <a,b>=c and P=<g,a>+<h,b> for vectors a,b (raw IPA);
//!   - poly-commit proves p(z)=v for a polynomial p (PCS via IPA).
//! Both reduce to the same Bulletproofs-style recursion: O(N) prover
//! work, O(N) full-check verifier work (one O(N) MSM after log(N) rounds).
//!
//! Vector size N = 2^S; sweep by varying S.
//!
//! The native side's `commit` is treated as setup (untimed) — analogous
//! to how zippel's `p_initial_commitment` is built as an input outside
//! the timed protocol.

use crate::Timing;

pub mod zippel_side {
    use super::*;
    use backend::{ATyp, ArkSecp256k1, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkSecp256k1>,
        n: usize,
    }

    impl Setup {
        pub fn new(s_const: usize) -> Self {
            let n = 1usize << s_const;
            let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/ipa/ipa.zippel");
            let args = ZippelArgs::new(zippel_file);
            let mut handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("S"), &s_const);
            handler.compile(&sizes);
            Setup { handler, n }
        }

        pub fn time_protocol(&mut self) -> Timing {
            let mut rng = rand::rngs::OsRng;
            let n = self.n;

            let u_aux_base = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::g1());
            let g_vec = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n));
            let h_vec = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n));
            let a_vec_witness =
                Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n));
            let b_vec_witness =
                Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n));
            let ip_val_claimed = a_vec_witness.clone().dot(b_vec_witness.clone());
            let p_initial_commitment =
                g_vec.clone().dot(a_vec_witness.clone()) + h_vec.clone().dot(b_vec_witness.clone());
            let sum_vec = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n));

            let inputs = Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
                (Vid("g_vec".to_string()), g_vec),
                (Vid("h_vec".to_string()), h_vec),
                (Vid("p_initial_commitment".to_string()), p_initial_commitment),
                (Vid("ip_val_claimed".to_string()), ip_val_claimed),
                (Vid("u_aux_base".to_string()), u_aux_base),
                (Vid("a_vec_witness".to_string()), a_vec_witness),
                (Vid("b_vec_witness".to_string()), b_vec_witness),
                (Vid("sum_vec".to_string()), sum_vec),
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
            assert!(result.passed, "zippel IPA verification FAILED");

            Timing { prove, verify }
        }
    }
}

pub mod native_side {
    use super::*;
    use np_ark_crypto_primitives::sponge::{
        CryptographicSponge,
        poseidon::{PoseidonConfig, PoseidonSponge},
    };
    use np_ark_ff::UniformRand;
    use np_ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
    use np_ark_poly_commit::{
        LabeledPolynomial, PolynomialCommitment, ipa_pc::InnerProductArgPC,
    };
    use np_ark_secp256k1::{Affine as SecpAffine, Fr};
    use std::time::Instant;

    type IpaPC = InnerProductArgPC<SecpAffine, blake2::Blake2s256, DensePolynomial<Fr>>;

    pub struct Setup {
        ck: <IpaPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
        vk: <IpaPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::VerifierKey,
        sponge_config: PoseidonConfig<Fr>,
        n: usize,
    }

    impl Setup {
        pub fn new(s_const: usize) -> Self {
            let n = 1usize << s_const;
            let mut rng = ark_std::test_rng();
            // max_degree = N - 1 means N coefficients, matching zippel's vector length N.
            let pp = IpaPC::setup(n - 1, None, &mut rng).expect("ipa setup");
            let (ck, vk) = IpaPC::trim(&pp, n - 1, 0, None).expect("ipa trim");
            Setup {
                ck,
                vk,
                sponge_config: poseidon_config(),
                n,
            }
        }

        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();
            let poly = DensePolynomial::<Fr>::rand(self.n - 1, &mut rng);
            let labeled =
                LabeledPolynomial::new("p".to_string(), poly.clone(), None, None);
            let (comms, states) = IpaPC::commit(&self.ck, [&labeled], Some(&mut rng))
                .expect("ipa commit");

            let point = Fr::rand(&mut rng);
            let value = poly.evaluate(&point);
            let mut sponge = PoseidonSponge::<Fr>::new(&self.sponge_config);

            let t = Instant::now();
            let proof = IpaPC::open(
                &self.ck,
                [&labeled],
                &comms,
                &point,
                &mut sponge,
                &states,
                Some(&mut rng),
            )
            .expect("ipa open");
            let prove = t.elapsed();

            let mut sponge = PoseidonSponge::<Fr>::new(&self.sponge_config);
            let t = Instant::now();
            let ok = IpaPC::check(
                &self.vk,
                &comms,
                &point,
                [value],
                &proof,
                &mut sponge,
                None,
            )
            .expect("ipa check");
            let verify = t.elapsed();

            assert!(ok, "ark-poly-commit IPA verification FAILED");

            Timing { prove, verify }
        }
    }

    /// Inlined copy of arkworks' test-only poseidon parameters
    /// (`poseidon_parameters_for_test` from ark-poly-commit). NOT
    /// cryptographically secure — fine for timing.
    fn poseidon_config() -> PoseidonConfig<Fr> {
        let full_rounds = 8;
        let partial_rounds = 31;
        let alpha = 17;

        let mds = vec![
            vec![Fr::from(1u64), Fr::from(0u64), Fr::from(1u64)],
            vec![Fr::from(1u64), Fr::from(1u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(1u64), Fr::from(1u64)],
        ];

        let mut rng = ark_std::test_rng();
        let mut ark = Vec::new();
        for _ in 0..(full_rounds + partial_rounds) {
            let row: Vec<Fr> = (0..3).map(|_| Fr::rand(&mut rng)).collect();
            ark.push(row);
        }
        PoseidonConfig::new(full_rounds, partial_rounds, alpha, mds, ark, 2, 1)
    }
}
