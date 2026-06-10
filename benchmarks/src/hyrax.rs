use crate::Timing;

pub const DEFAULT_N: usize = 10;

pub mod zippel_side {
    use super::Timing;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ec::CurveGroup;
    use ark_ff::{One, Zero};
    use ark_std::UniformRand;
    use ark_std::rand::SeedableRng;
    use backend::{ArkBls12_381, Value};
    use lang::id::Vid;
    use share::Ctx;
    use std::io::Write;
    use std::time::Instant;
    use tempfile::NamedTempFile;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        inputs: Ctx<Vid, Value<ArkBls12_381>>,
        _source_file: NamedTempFile,
    }

    impl Setup {
        pub fn new(n: usize) -> Self {
            assert!(
                n >= 2 && n <= 20 && n % 2 == 0,
                "n must be an even number in 2..=20 (eq_weights cap)"
            );
            let l = n / 2;
            let m = n - l;
            let nrows = 1usize << l;
            let ncols = 1usize << m;
            let ntot = nrows * ncols;

            let mut source_file = NamedTempFile::with_suffix(".zippel").expect("tempfile");
            source_file
                .write_all(render_proto(l, m).as_bytes())
                .expect("write tempfile");

            let mut seed_bytes = [0u8; 32];
            seed_bytes[..8].copy_from_slice(&(0xFEEDFACE_u64 ^ n as u64).to_le_bytes());
            let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);

            let p: Vec<Fr> = (0..ntot).map(|_| Fr::rand(&mut rng)).collect();
            let z_row: Vec<Fr> = (0..l).map(|_| Fr::rand(&mut rng)).collect();
            let z_col: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();

            let l_vec = eq_evals_lsb(&z_row);
            let r_vec = eq_evals_lsb(&z_col);
            let mut y = Fr::zero();
            for i in 0..nrows {
                for j in 0..ncols {
                    y += l_vec[i] * r_vec[j] * p[i * ncols + j];
                }
            }

            let g_proj: Vec<G1Projective> =
                (0..ncols).map(|_| G1Projective::rand(&mut rng)).collect();
            let g_vec_aff = G1Projective::normalize_batch(&g_proj);
            let g_base = G1Projective::rand(&mut rng);
            let h_base = G1Projective::rand(&mut rng);

            let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("p".to_string()), Value::VecScalar(p)),
                (Vid("z_row".to_string()), Value::VecScalar(z_row)),
                (Vid("z_col".to_string()), Value::VecScalar(z_col)),
                (Vid("y".to_string()), Value::Scalar(y)),
                (Vid("g_vec".to_string()), Value::VecG1Affine(g_vec_aff)),
                (Vid("g_base".to_string()), Value::G1(g_base)),
                (Vid("h_base".to_string()), Value::G1(h_base)),
            ]);

            let args = ZippelArgs::new(source_file.path().to_path_buf());
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            handler.compile(&Ctx::new());

            Setup {
                handler,
                inputs,
                _source_file: source_file,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            let prover_scheduled = self.handler.default_schedule_prover();
            let t = Instant::now();
            let proof = self
                .handler
                .run_prover(prover_scheduled, self.inputs.clone())
                .expect("zippel hyrax prover failed");
            let prove = t.elapsed();

            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("zippel hyrax verifier failed");
            let verify = t.elapsed();
            let result = check_verification(verifier_result);
            assert!(result.passed, "zippel hyrax verification FAILED");
            Timing { prove, verify }
        }

        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.handler.prover_graph.as_ref().unwrap().node_count(),
                self.handler.verifier_graph.as_ref().unwrap().node_count(),
            )
        }
    }

    fn eq_evals_lsb(x: &[Fr]) -> Vec<Fr> {
        let n = x.len();
        let one = Fr::one();
        let mut out = vec![one; 1 << n];
        let mut size = 1;
        for &xi in x {
            let one_m_xi = one - xi;
            for i in (0..size).rev() {
                let v = out[i];
                out[size + i] = v * xi;
                out[i] = v * one_m_xi;
            }
            size *= 2;
        }
        out
    }

    fn render_proto(l: usize, m: usize) -> String {
        let nrows = 1usize << l;
        let ncols = 1usize << m;
        let ntot = nrows * ncols;
        format!(
            r#"fn eq_weights<G: Group, F: Scalar<G>>(public x: [F; 1]) -> [F; 2] {{
    [ (1 - x[0]), x[0] ]
}}

fn eq_weights<G: Group, F: Scalar<G>, K: 2..21>(public x: [F; K]) -> [F; 2^K] {{
    let x_lo = x[0..(K-1)];
    let a    = x[K-1];
    let prev = eq_weights(x_lo);
    (prev * (1 - a)) ++ (prev * a)
}}

proto hyrax<G: Group, F: Scalar<G>>(
    private p:     [F; {ntot}],
    public z_row:  [F; {l}],
    public z_col:  [F; {m}],
    public y:      F,
    public g_vec:  [G; {ncols}],
    public g_base: G,
    public h_base: G
) where g_base == g_base
{{
    let r_rows = [random<F> for i in 0..{nrows}];
    c_rows <- [
        h_base * r_rows[i] + dot(g_vec, [p[i*{ncols} + j] for j in 0..{ncols}])
        for i in 0..{nrows}
    ];

    let l_vec = eq_weights(z_row);
    let r_vec = eq_weights(z_col);
    let big_t   = dot(l_vec, c_rows);
    let r_big_t = dot(l_vec, r_rows);
    let u = [
        dot(l_vec, [p[i*{ncols} + j] for i in 0..{nrows}])
        for j in 0..{ncols}
    ];

    let r_tau   = random<F>;
    let d_vec   = [random<F> for i in 0..{ncols}];
    let r_delta = random<F>;
    let r_beta  = random<F>;

    tau   <- g_base * y + h_base * r_tau;
    delta <- h_base * r_delta + dot(g_vec, d_vec);
    beta  <- g_base * dot(d_vec, r_vec) + h_base * r_beta;

    c <- challenge<F>;

    z_vec   <- [c * u[i] + d_vec[i] for i in 0..{ncols}];
    z_delta <- c * r_big_t + r_delta;
    z_beta  <- c * r_tau + r_beta;

    let check1 = big_t * c + delta == h_base * z_delta + dot(g_vec, z_vec);
    let check2 = tau   * c + beta  == g_base * dot(z_vec, r_vec) + h_base * z_beta;
    verify(check1 && check2)
}}
"#
        )
    }
}

/// Native Hyrax baseline: `ark_poly_commit::hyrax::HyraxPC` (v0.5.0 on
/// crates.io, pulled via the `np-ark-*` 0.5-island aliases). Multilinear
/// PCS with a Poseidon-based Fiat-Shamir transcript — the same
/// PoseidonConfig the upstream `bench-templates::test_sponge` uses.
/// Timed regions match the zippel side: prove = commit + open (row
/// Pedersens + σ-protocol), verify = check.
pub mod native_side {
    use super::Timing;
    use np_ark_bls12_381::{Fr, G1Affine};
    use np_ark_crypto_primitives::sponge::{
        poseidon::{PoseidonConfig, PoseidonSponge},
        CryptographicSponge,
    };
    use np_ark_ff::{One, PrimeField, UniformRand, Zero};
    use np_ark_poly::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use np_ark_poly_commit::{
        hyrax::HyraxPC, LabeledPolynomial, PolynomialCommitment,
    };
    use std::time::Instant;

    type Hyrax = HyraxPC<G1Affine, DenseMultilinearExtension<Fr>>;
    type CK = <Hyrax as PolynomialCommitment<Fr, DenseMultilinearExtension<Fr>>>::CommitterKey;
    type VK = <Hyrax as PolynomialCommitment<Fr, DenseMultilinearExtension<Fr>>>::VerifierKey;

    pub struct Setup {
        num_vars: usize,
        ck: CK,
        vk: VK,
    }

    impl Setup {
        pub fn new(n: usize) -> Self {
            let mut rng = ark_std::test_rng();
            let pp = Hyrax::setup(n, Some(n), &mut rng).expect("hyrax setup");
            let (ck, vk) = Hyrax::trim(&pp, n, n, None).expect("hyrax trim");
            Setup { num_vars: n, ck, vk }
        }

        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();
            let poly = DenseMultilinearExtension::<Fr>::rand(self.num_vars, &mut rng);
            let labeled =
                LabeledPolynomial::new("hyrax_bench".to_string(), poly, None, None);
            let point: Vec<Fr> = (0..self.num_vars).map(|_| Fr::rand(&mut rng)).collect();
            let value = labeled.evaluate(&point);

            // Prove = commit + open. Mirrors the zippel side, which
            // synthesizes c_rows (row Pedersens) and the σ-protocol
            // triple (τ, δ, β) + responses inside one timed region.
            let t = Instant::now();
            let (coms, states) =
                Hyrax::commit(&self.ck, [&labeled], Some(&mut rng)).expect("hyrax commit");
            let mut sponge = test_sponge::<Fr>();
            let proof = Hyrax::open(
                &self.ck,
                [&labeled],
                &coms,
                &point,
                &mut sponge,
                &states,
                Some(&mut rng),
            )
            .expect("hyrax open");
            let prove = t.elapsed();

            let t = Instant::now();
            let mut sponge_v = test_sponge::<Fr>();
            let ok = Hyrax::check(
                &self.vk,
                &coms,
                &point,
                [value],
                &proof,
                &mut sponge_v,
                None,
            )
            .expect("hyrax check");
            let verify = t.elapsed();
            assert!(ok, "upstream Hyrax verification FAILED");

            let _ = (Fr::one(), Fr::zero());
            Timing { prove, verify }
        }
    }

    // Verbatim from ark-poly-commit-0.5.0 bench-templates/src/lib.rs::test_sponge.
    fn test_sponge<F: PrimeField>() -> PoseidonSponge<F> {
        let full_rounds = 8;
        let partial_rounds = 31;
        let alpha = 17;
        let mds = vec![
            vec![F::one(), F::zero(), F::one()],
            vec![F::one(), F::one(), F::zero()],
            vec![F::zero(), F::one(), F::one()],
        ];
        let mut v = Vec::new();
        let mut ark_rng = ark_std::test_rng();
        for _ in 0..(full_rounds + partial_rounds) {
            let mut res = Vec::new();
            for _ in 0..3 {
                res.push(F::rand(&mut ark_rng));
            }
            v.push(res);
        }
        let config =
            PoseidonConfig::new(full_rounds, partial_rounds, alpha, mds, v, 2, 1);
        PoseidonSponge::new(&config)
    }
}
