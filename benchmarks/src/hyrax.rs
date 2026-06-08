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

pub mod native_side {
    use super::Timing;
    use ark_bls12_381::{Fr, G1Affine, G1Projective};
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_ff::{Field, One, PrimeField, Zero};
    use ark_std::UniformRand;
    use ark_std::rand::SeedableRng;
    use blake2::{Blake2b512, Digest};
    use std::time::Instant;

    pub struct Setup {
        n: usize,
        l: usize,
        m: usize,
        nrows: usize,
        ncols: usize,
        g_vec_aff: Vec<G1Affine>,
        g_base: G1Projective,
        h_base: G1Projective,
    }

    impl Setup {
        pub fn new(n: usize) -> Self {
            assert!(n >= 2 && n % 2 == 0, "n must be even and >= 2");
            let l = n / 2;
            let m = n - l;
            let nrows = 1usize << l;
            let ncols = 1usize << m;

            let mut seed_bytes = [0u8; 32];
            seed_bytes[..8].copy_from_slice(&(0xCAFEBABE_u64 ^ n as u64).to_le_bytes());
            let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);

            let g_vec_proj: Vec<G1Projective> =
                (0..ncols).map(|_| G1Projective::rand(&mut rng)).collect();
            let g_vec_aff = G1Projective::normalize_batch(&g_vec_proj);
            let g_base = G1Projective::rand(&mut rng);
            let h_base = G1Projective::rand(&mut rng);

            Setup {
                n,
                l,
                m,
                nrows,
                ncols,
                g_vec_aff,
                g_base,
                h_base,
            }
        }

        pub fn time_protocol(&self) -> Timing {
            let mut seed_bytes = [0u8; 32];
            seed_bytes[..8].copy_from_slice(&(0xC0DEC0DE_u64 ^ self.n as u64).to_le_bytes());
            let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);

            let ntot = self.nrows * self.ncols;
            let p: Vec<Fr> = (0..ntot).map(|_| Fr::rand(&mut rng)).collect();
            let z_row: Vec<Fr> = (0..self.l).map(|_| Fr::rand(&mut rng)).collect();
            let z_col: Vec<Fr> = (0..self.m).map(|_| Fr::rand(&mut rng)).collect();

            let l_vec = eq_evals_lsb(&z_row);
            let r_vec = eq_evals_lsb(&z_col);
            let y: Fr = (0..self.nrows)
                .flat_map(|i| (0..self.ncols).map(move |j| (i, j)))
                .map(|(i, j)| l_vec[i] * r_vec[j] * p[i * self.ncols + j])
                .sum();

            let r_rows: Vec<Fr> = (0..self.nrows).map(|_| Fr::rand(&mut rng)).collect();
            let r_tau = Fr::rand(&mut rng);
            let d_vec: Vec<Fr> = (0..self.ncols).map(|_| Fr::rand(&mut rng)).collect();
            let r_delta = Fr::rand(&mut rng);
            let r_beta = Fr::rand(&mut rng);

            let t = Instant::now();

            let mut c_rows_proj: Vec<G1Projective> = Vec::with_capacity(self.nrows);
            for i in 0..self.nrows {
                let row_bi: Vec<<Fr as PrimeField>::BigInt> = (0..self.ncols)
                    .map(|j| p[i * self.ncols + j].into_bigint())
                    .collect();
                let g_row = G1Projective::msm_bigint(&self.g_vec_aff, &row_bi);
                c_rows_proj.push(self.h_base * r_rows[i] + g_row);
            }
            let c_rows_aff = G1Projective::normalize_batch(&c_rows_proj);

            let mut u: Vec<Fr> = vec![Fr::zero(); self.ncols];
            for i in 0..self.nrows {
                let li = l_vec[i];
                for j in 0..self.ncols {
                    u[j] += li * p[i * self.ncols + j];
                }
            }
            let r_big_t: Fr = (0..self.nrows).map(|i| l_vec[i] * r_rows[i]).sum();

            let tau = self.g_base * y + self.h_base * r_tau;
            let d_bi: Vec<<Fr as PrimeField>::BigInt> =
                d_vec.iter().map(|x| x.into_bigint()).collect();
            let g_d = G1Projective::msm_bigint(&self.g_vec_aff, &d_bi);
            let delta = self.h_base * r_delta + g_d;
            let dot_d_r: Fr = (0..self.ncols).map(|j| d_vec[j] * r_vec[j]).sum();
            let beta = self.g_base * dot_d_r + self.h_base * r_beta;

            let c = fs_challenge(
                &self.g_base,
                &self.h_base,
                &self.g_vec_aff,
                &z_row,
                &z_col,
                &y,
                &c_rows_aff,
                &tau,
                &delta,
                &beta,
            );

            let z_vec: Vec<Fr> = (0..self.ncols).map(|j| c * u[j] + d_vec[j]).collect();
            let z_delta = c * r_big_t + r_delta;
            let z_beta = c * r_tau + r_beta;

            let prove = t.elapsed();

            let t = Instant::now();

            let c_v = fs_challenge(
                &self.g_base,
                &self.h_base,
                &self.g_vec_aff,
                &z_row,
                &z_col,
                &y,
                &c_rows_aff,
                &tau,
                &delta,
                &beta,
            );
            assert_eq!(c, c_v);

            let l_bi: Vec<<Fr as PrimeField>::BigInt> =
                l_vec.iter().map(|x| x.into_bigint()).collect();
            let big_t = G1Projective::msm_bigint(&c_rows_aff, &l_bi);

            let z_bi: Vec<<Fr as PrimeField>::BigInt> =
                z_vec.iter().map(|x| x.into_bigint()).collect();
            let g_z = G1Projective::msm_bigint(&self.g_vec_aff, &z_bi);
            let lhs1 = big_t * c + delta;
            let rhs1 = self.h_base * z_delta + g_z;
            let check1 = lhs1 == rhs1;

            let dot_z_r: Fr = (0..self.ncols).map(|j| z_vec[j] * r_vec[j]).sum();
            let lhs2 = tau * c + beta;
            let rhs2 = self.g_base * dot_z_r + self.h_base * z_beta;
            let check2 = lhs2 == rhs2;

            let ok = check1 && check2;
            let verify = t.elapsed();
            assert!(ok, "native Hyrax verification FAILED");

            let _ = (c_rows_aff.len(), big_t);

            Timing { prove, verify }
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

    #[allow(clippy::too_many_arguments)]
    fn fs_challenge(
        g_base: &G1Projective,
        h_base: &G1Projective,
        g_vec: &[G1Affine],
        z_row: &[Fr],
        z_col: &[Fr],
        y: &Fr,
        c_rows: &[G1Affine],
        tau: &G1Projective,
        delta: &G1Projective,
        beta: &G1Projective,
    ) -> Fr {
        use ark_serialize::CanonicalSerialize;
        fn absorb<T: CanonicalSerialize>(t: &T, h: &mut Blake2b512, buf: &mut Vec<u8>) {
            buf.clear();
            t.serialize_compressed(&mut *buf).unwrap();
            h.update(&buf);
        }
        let mut h = Blake2b512::new();
        let mut buf = Vec::with_capacity(96);
        absorb(g_base, &mut h, &mut buf);
        absorb(h_base, &mut h, &mut buf);
        absorb(&g_vec.to_vec(), &mut h, &mut buf);
        absorb(&z_row.to_vec(), &mut h, &mut buf);
        absorb(&z_col.to_vec(), &mut h, &mut buf);
        absorb(y, &mut h, &mut buf);
        absorb(&c_rows.to_vec(), &mut h, &mut buf);
        absorb(tau, &mut h, &mut buf);
        absorb(delta, &mut h, &mut buf);
        absorb(beta, &mut h, &mut buf);
        Fr::from_le_bytes_mod_order(&h.finalize())
    }
}
