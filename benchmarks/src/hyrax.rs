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
        compile_time: std::time::Duration,
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

            // Time the zippel compiler: source → executable graph.
            // Includes parsing, type-checking, and graph construction.
            // Excludes runtime scheduling (which is per-call cheap
            // graph→TDag work the runtime does) and excludes the actual
            // prove/verify execution.
            let compile_start = Instant::now();
            let args = ZippelArgs::new(source_file.path().to_path_buf());
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            handler.compile(&Ctx::new());
            let compile_time = compile_start.elapsed();

            Setup {
                handler,
                inputs,
                _source_file: source_file,
                compile_time,
            }
        }

        pub fn compile_time(&self) -> std::time::Duration {
            self.compile_time
        }

        pub fn time_protocol(&mut self) -> Timing {
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let inputs_c = self.inputs.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(&inputs_c)
                    .expect("zippel hyrax prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(&proof_c)
                    .expect("zippel hyrax verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            let result = check_verification(last_result.expect("VERIFY_SAMPLES > 0"));
            assert!(result.passed, "zippel hyrax verification FAILED");
            Timing { prove, verify }
        }

        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.handler.prover_graph().node_count(),
                self.handler.verifier_graph().node_count(),
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

    pub fn render_proto(l: usize, m: usize) -> String {
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
) where
    // Hyrax proves y == p̃(z_row, z_col), where p̃ is the multilinear
    // extension of `p` indexed row-major as a {nrows}×{ncols} matrix.
    // Flatten the tensored eq-basis over (z_row, z_col) into one vector
    // so the relation is a single dot product against `p`, matching how
    // pst13.zippel expresses `y == dot(eq_mle(z), p)`.
    let l_vec = eq_weights(z_row);
    let r_vec = eq_weights(z_col);
    let eq_full = [l_vec[i / {ncols}] * r_vec[i % {ncols}] for i in 0..{ntot}];
    y == dot(eq_full, p)
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

/// Native Hyrax baseline. Vendored from `ark-poly-commit-0.6.0::hyrax`
/// (see `crate::hyrax_upstream`) with the matrix-vector multiplication
/// in `open` rewritten to use flat row-major storage and a SAXPY
/// accumulation — upstream's `Matrix<F>` stores rows as separately
/// allocated `Vec<F>`s and `Matrix::row_mul` allocates a fresh 16KB
/// column-gather Vec per output element (8MB churn at log_size=18) plus
/// nested `par_iter` overhead. Crypto primitives and Fiat-Shamir
/// transcript bytes are unchanged. Timed regions still match the zippel
/// side: prove = commit + open (row Pedersens + σ-protocol),
/// verify = check.
pub mod native_side {
    use super::Timing;
    use ark_bls12_381::{Fr, G1Affine};
    use ark_crypto_primitives::sponge::{
        poseidon::{PoseidonConfig, PoseidonSponge},
        CryptographicSponge,
    };
    use ark_ff::{PrimeField, UniformRand};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use std::time::Instant;

    use crate::hyrax_upstream::{
        self, CommitterKey, VerifierKey,
    };

    pub struct Setup {
        _num_vars: usize,
        ck: CommitterKey,
        vk: VerifierKey,
        poly: DenseMultilinearExtension<Fr>,
        point: Vec<Fr>,
        value: Fr,
    }

    impl Setup {
        pub fn new(n: usize) -> Self {
            // Cache UniversalParams. Byte format matches upstream's
            // derived CanonicalSerialize (same field order: com_key, h),
            // so caches written by either implementation interoperate.
            let pp = crate::cache::load_or_build_canonical::<
                ark_poly_commit::hyrax::HyraxUniversalParams<G1Affine>,
            >("hyrax_universal_params", n, || {
                let mut rng = ark_std::test_rng();
                hyrax_upstream::setup(n, &mut rng)
            });
            let (ck, vk) = hyrax_upstream::trim(&pp);

            // Poly/point/value generation runs in `setup_pool` (called
            // here, not in time_protocol). At log_size=20 the rand poly
            // is 2^20 field elements and `evaluate` is O(2^n) — keeping
            // this in the bench pool single-threaded at threads=1 was
            // wasting ~60ms per sweep iteration.
            let mut rng = ark_std::test_rng();
            let poly = DenseMultilinearExtension::<Fr>::rand(n, &mut rng);
            let point: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let value = poly.evaluate(&point);

            Setup {
                _num_vars: n,
                ck,
                vk,
                poly,
                point,
                value,
            }
        }

        pub fn time_protocol(&self) -> Timing {
            let point = &self.point;
            let _ = self.value;

            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_outputs = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let t = Instant::now();
                let (com, state) = hyrax_upstream::commit(&self.ck, &self.poly);
                let mut sponge = test_sponge::<Fr>();
                let proof = hyrax_upstream::open(&self.ck, &com, point, &mut sponge, &state);
                prove_sum += t.elapsed();
                last_outputs = Some((com, proof));
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let (com, proof) = last_outputs.expect("PROVER_SAMPLES > 0");

            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_ok = false;
            for _ in 0..crate::VERIFY_SAMPLES {
                let mut sponge_v = test_sponge::<Fr>();
                let t = Instant::now();
                let ok = hyrax_upstream::check(&self.vk, &com, point, &proof, &mut sponge_v);
                verify_sum += t.elapsed();
                last_ok = ok;
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            assert!(last_ok, "vendored Hyrax verification FAILED");

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
