use backend::{ArkBls12_381, ArkCurve25519, ArkSecp256k1};
use lang::id::Tid;
use share::Ctx;
use std::path::PathBuf;
use std::time::Instant;
use zippel::*;

fn compile_protocol<C: backend::ArkConfig + backend::HasOpFactory>(
    name: &str,
    zippel_path: PathBuf,
    sizes: Ctx<Tid, usize>,
) -> f64 {
    let start_total = Instant::now();
    let args = ZippelArgs::new(zippel_path);
    let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
    handler.compile(&sizes);
    
    let elapsed = start_total.elapsed().as_secs_f64();
    println!("Compiled {:<25} in {:.4} seconds", name, elapsed);
    elapsed
}

fn hyrax_split(m: usize) -> (usize, usize) {
    let nw = m - 1;
    let l = nw / 2;
    let m_h = nw - l;
    (l, m_h)
}

fn generate_proto(m: usize) -> String {
    let m_lit = m;
    let two_m = 1usize << m;
    let two_m_vars = 2 * m;
    let nw = m - 1;
    let two_nw = 1usize << nw;
    let io_len = two_nw - 1;
    let (l, m_h) = hyrax_split(m);
    let nrows = 1usize << l;
    let ncols = 1usize << m_h;
    assert_eq!(nrows * ncols, two_nw);

    format!(r#"fn eq_weights<G: Group, F: Scalar<G>>(public x: [F; 1]) -> [F; 2] {{
    [(1 - x[0]), x[0]]
}}
fn eq_weights<G: Group, F: Scalar<G>, EK: 2..21>(public x: [F; EK]) -> [F; 2^EK] {{
    let x_lo = x[0..(EK-1)];
    let a    = x[EK-1];
    let prev = eq_weights(x_lo);
    (prev * (1 - a)) ++ (prev * a)
}}

fn draw_taus<G: Group, F: Scalar<G>>(public placeholder: [F; 1]) -> [F; 1] {{
    t <- challenge<F>;
    [t]
}}
fn draw_taus<G: Group, F: Scalar<G>, DK: 2..21>(public placeholder: [F; DK]) -> [F; DK] {{
    let prev = draw_taus(placeholder[0..(DK-1)]);
    t <- challenge<F>;
    prev ++ [t]
}}

fn sc_recurse_d3<G: Group, F: Scalar<G>, SC: Size, V: 2..SC>(
    public curr_poly:       Poly<F, V, 3>,
    public points:          [F; 4],
    public prev_challenges: [F; SC - V],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d3:        [G; 4],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 3, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_next <- challenge<F>;
    let next_vec = eval(g, [r_next]);
    let next_prev = next_vec[0];
    let new_challenges = prev_challenges ++ [r_next];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d3, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d3[0] * next_prev + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..4];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d3, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d3[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..4];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d3, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    sc_recurse_d3(out.next_poly, points, new_challenges, next_prev, r_next, curr_round + 1, g_evs_d3, h_evs)
}}
fn sc_recurse_d3<G: Group, F: Scalar<G>, SC: Size>(
    public curr_poly:       Poly<F, 1, 3>,
    public points:          [F; 4],
    public prev_challenges: [F; SC - 1],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d3:        [G; 4],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 3, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_final <- challenge<F>;
    let final_vec = eval(g, [r_final]);
    let final_eval = final_vec[0];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d3, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d3[0] * final_eval + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..4];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d3, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d3[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..4];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d3, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    {{| final_eval: final_eval, challenges: prev_challenges ++ [r_final] |}}
}}

fn sc_recurse_d2<G: Group, F: Scalar<G>, SC: Size, V: 2..SC>(
    public curr_poly:       Poly<F, V, 2>,
    public points:          [F; 3],
    public prev_challenges: [F; SC - V],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d2:        [G; 3],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 2, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_next <- challenge<F>;
    let next_vec = eval(g, [r_next]);
    let next_prev = next_vec[0];
    let new_challenges = prev_challenges ++ [r_next];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d2, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d2[0] * next_prev + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..3];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d2, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d2[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..3];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d2, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    sc_recurse_d2(out.next_poly, points, new_challenges, next_prev, r_next, curr_round + 1, g_evs_d2, h_evs)
}}
fn sc_recurse_d2<G: Group, F: Scalar<G>, SC: Size>(
    public curr_poly:       Poly<F, 1, 2>,
    public points:          [F; 3],
    public prev_challenges: [F; SC - 1],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d2:        [G; 3],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 2, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_final <- challenge<F>;
    let final_vec = eval(g, [r_final]);
    let final_eval = final_vec[0];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d2, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d2[0] * final_eval + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..3];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d2, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d2[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..3];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d2, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    {{| final_eval: final_eval, challenges: prev_challenges ++ [r_final] |}}
}}

fn compute_s_vec<G: Group, F: Scalar<G>>(public c: [F; 1], public c_inv: [F; 1]) -> [F; 2] {{
    [c_inv[0], c[0]]
}}
fn compute_s_vec<G: Group, F: Scalar<G>, K: 2..21>(public c: [F; K], public c_inv: [F; K]) -> [F; 2^K] {{
    let curr_c = c[0];
    let curr_c_inv = c_inv[0];
    let c_rest = c[1..K];
    let c_inv_rest = c_inv[1..K];
    let prev = compute_s_vec(c_rest, c_inv_rest);
    (prev * curr_c_inv) ++ (prev * curr_c)
}}

fn bullet_collect<G: Group, F: Scalar<G>>(
    public g_base: G,
    public h_base: G,
    private g_folded: [G; 2],
    private a_folded: [F; 2],
    private x_folded: [F; 2],
    private y_folded: F,
    private r_Upsilon_folded: F
) -> {{ challenges: [F; 1], challenges_inv: [F; 1], Ls: [G; 1], Rs: [G; 1], final_x: F, final_y: F, final_r: F }} {{
    let x_1 = x_folded[0..1];
    let x_2 = x_folded[1..2];
    let a_1 = a_folded[0..1];
    let a_2 = a_folded[1..2];
    let g_1 = g_folded[0..1];
    let g_2 = g_folded[1..2];
    let r_L = random<F>;
    let r_R = random<F>;
    let dot_x1_a2 = dot(x_1, a_2);
    let dot_x2_a1 = dot(x_2, a_1);
    upsilon_neg1 <- h_base * r_L + g_base * dot_x1_a2 + dot(g_2, x_1);
    upsilon_1 <- h_base * r_R + g_base * dot_x2_a1 + dot(g_1, x_2);
    c <- challenge<F>;
    let c_inv = 1 / c;
    let c_sq = c * c;
    let c_inv_sq = c_inv * c_inv;
    let next_x = x_1 * c + x_2 * c_inv;
    let next_y = dot_x1_a2 * c_sq + y_folded + dot_x2_a1 * c_inv_sq;
    let next_r = r_L * c_sq + r_Upsilon_folded + r_R * c_inv_sq;
    {{|
        challenges: [c],
        challenges_inv: [c_inv],
        Ls: [upsilon_neg1],
        Rs: [upsilon_1],
        final_x: next_x[0],
        final_y: next_y,
        final_r: next_r
    |}}
}}

fn bullet_collect<G: Group, F: Scalar<G>, S: Size, N: 2..S+1>(
    public g_base: G,
    public h_base: G,
    private g_folded: [G; 2^N],
    private a_folded: [F; 2^N],
    private x_folded: [F; 2^N],
    private y_folded: F,
    private r_Upsilon_folded: F
) -> {{ challenges: [F; N], challenges_inv: [F; N], Ls: [G; N], Rs: [G; N], final_x: F, final_y: F, final_r: F }} {{
    let x_1 = x_folded[0..2^(N-1)];
    let x_2 = x_folded[2^(N-1)..2^N];
    let a_1 = a_folded[0..2^(N-1)];
    let a_2 = a_folded[2^(N-1)..2^N];
    let g_1 = g_folded[0..2^(N-1)];
    let g_2 = g_folded[2^(N-1)..2^N];
    let r_L = random<F>;
    let r_R = random<F>;
    let dot_x1_a2 = dot(x_1, a_2);
    let dot_x2_a1 = dot(x_2, a_1);
    upsilon_neg1 <- h_base * r_L + g_base * dot_x2_a1 + dot(g_2, x_1);
    upsilon_1 <- h_base * r_R + g_base * dot_x2_a1 + dot(g_1, x_2);
    c <- challenge<F>;
    let c_inv = 1 / c;
    let c_sq = c * c;
    let c_inv_sq = c_inv * c_inv;
    let next_g = g_1 * c_inv + g_2 * c;
    let next_a = a_1 * c_inv + a_2 * c;
    let next_x = x_1 * c + x_2 * c_inv;
    let next_y = dot_x1_a2 * c_sq + y_folded + dot_x2_a1 * c_inv_sq;
    let next_r = r_L * c_sq + r_Upsilon_folded + r_R * c_inv_sq;
    let inner = bullet_collect(g_base, h_base, next_g, next_a, next_x, next_y, next_r);
    {{|
        challenges: [c] ++ inner.challenges,
        challenges_inv: [c_inv] ++ inner.challenges_inv,
        Ls: [upsilon_neg1] ++ inner.Ls,
        Rs: [upsilon_1] ++ inner.Rs,
        final_x: inner.final_x,
        final_y: inner.final_y,
        final_r: inner.final_r
    |}}
}}

proto spartan<G: Group, F: Scalar<G>>(
    public mat_a_t:   Poly<F, {two_m_vars}, 1>,
    public mat_b_t:   Poly<F, {two_m_vars}, 1>,
    public mat_c_t:   Poly<F, {two_m_vars}, 1>,
    public io:        [F; {io_len}],
    private w:        [F; {two_nw}],
    private az:       [F; {two_m}],
    private bz:       [F; {two_m}],
    private cz:       [F; {two_m}],
    public g_vec_w:   [G; {ncols}],
    public g_base_w:  G,
    public h_base_w:  G,
    public g_evs_d3:  [G; 4],
    public g_evs_d2:  [G; 3],
    public h_evs:     G,
    public placeholder_tau: [F; {m_lit}],
    public f_one:     F
) where
    az * bz == cz
{{
    let one  = f_one;
    let zero = f_one - f_one;

    let r_rows = [random<F> for i in 0..{nrows}];
    c_rows <- [
        h_base_w * r_rows[i] + dot(g_vec_w, [w[i*{ncols} + j] for j in 0..{ncols}])
        for i in 0..{nrows}
    ];

    let z = w ++ io ++ [one];

    let f_a = mle(az);
    let f_b = mle(bz);
    let f_c = mle(cz);

    let tau_vec = draw_taus(placeholder_tau);
    let eq_tau_evs = eq_weights(tau_vec);
    let eq_tau     = mle(eq_tau_evs);

    let neg_one = zero - one;
    let g_sub   = f_a * f_b + f_c * neg_one;
    let g_poly  = g_sub * eq_tau;

    let pts3   = [i for i in 0..4];
    let cfg1_0 = {{| poly: g_poly, num_variables: {m_lit}, max_degree: 3, round: 0, challenge: zero |}};
    let out1_0 = marginalize(cfg1_0);
    evs1_0 <- out1_0.evaluations;
    verify(zero == evs1_0[0] + evs1_0[1]);
    let g1_r1     = interpolate(pts3, evs1_0);
    rx0           <- challenge<F>;
    let prev1_vec = eval(g1_r1, [rx0]);
    let prev1     = prev1_vec[0];

    let r_poly_10 = random<F>;
    comm_evs_10 <- dot(g_evs_d3, evs1_0) + h_evs * r_poly_10;
    let r_eval_10 = random<F>;
    comm_eval_10 <- g_evs_d3[0] * prev1 + h_evs * r_eval_10;
    let d_vec_10 = [random<F> for i in 0..4];
    let r_delta_10 = random<F>;
    let r_beta_10  = random<F>;
    delta_10 <- dot(g_evs_d3, d_vec_10) + h_evs * r_delta_10;
    let a_d_dot_10 = dot(d_vec_10, evs1_0);
    beta_10  <- g_evs_d3[0] * a_d_dot_10 + h_evs * r_beta_10;
    c_10     <- challenge<F>;
    z_vec_10   <- [c_10 * evs1_0[i] + d_vec_10[i] for i in 0..4];
    z_delta_10 <- c_10 * r_poly_10 + r_delta_10;
    z_beta_10  <- c_10 * r_eval_10 + r_beta_10;
    let zk_check_10 = dot(g_evs_d3, z_vec_10) + h_evs * z_delta_10 == comm_evs_10 * c_10 + delta_10;
    verify(zk_check_10);

    let sc1 = sc_recurse_d3(out1_0.next_poly, pts3, [rx0], prev1, rx0, 1, g_evs_d3, h_evs);
    let rx  = sc1.challenges;
    let e_x = sc1.final_eval;

    let lx = eq_weights(rx);
    v_a <- dot(lx, az);
    v_b <- dot(lx, bz);
    v_c <- dot(lx, cz);
    let eq_tau_at_rx = dot(lx, eq_tau_evs);
    verify(e_x == (v_a * v_b - v_c) * eq_tau_at_rx);

    let r_va = random<F>;
    let r_vb = random<F>;
    let r_vc = random<F>;
    let r_prod = random<F>;
    comm_va_phase1 <- g_evs_d3[0] * v_a + h_evs * r_va;
    comm_vb_phase1 <- g_evs_d3[0] * v_b + h_evs * r_vb;
    comm_vc_phase1 <- g_evs_d3[0] * v_c + h_evs * r_vc;
    comm_prod_phase1 <- g_evs_d3[0] * (v_a * v_b) + h_evs * r_prod;
    let d1_phase1 = random<F>;
    let d2_phase1 = random<F>;
    let r_d_phase1 = random<F>;
    let r_e_phase1 = random<F>;
    let r_f_phase1 = random<F>;
    alpha_phase1 <- g_evs_d3[0] * d1_phase1 + h_evs * r_d_phase1;
    beta_p1_phase1 <- g_evs_d3[0] * d2_phase1 + h_evs * r_e_phase1;
    delta_phase1 <- comm_va_phase1 * d2_phase1 + h_evs * r_f_phase1;
    c_phase1 <- challenge<F>;
    z1_phase1 <- c_phase1 * v_a + d1_phase1;
    z2_phase1 <- c_phase1 * r_va + r_d_phase1;
    z3_phase1 <- c_phase1 * v_b + d2_phase1;
    z4_phase1 <- c_phase1 * r_vb + r_e_phase1;
    z5_phase1 <- c_phase1 * (r_prod - r_va * v_b) + r_f_phase1;
    let prod_check1 = g_evs_d3[0] * z1_phase1 + h_evs * z2_phase1 == comm_va_phase1 * c_phase1 + alpha_phase1;
    let prod_check2 = g_evs_d3[0] * z3_phase1 + h_evs * z4_phase1 == comm_vb_phase1 * c_phase1 + beta_p1_phase1;
    let prod_check3 = comm_va_phase1 * z3_phase1 + h_evs * z5_phase1 == comm_prod_phase1 * c_phase1 + delta_phase1;
    verify(prod_check1);
    verify(prod_check2);
    verify(prod_check3);
    let t1_pok_vc = random<F>;
    let t2_pok_vc = random<F>;
    alpha_pok_vc <- g_evs_d3[0] * t1_pok_vc + h_evs * t2_pok_vc;
    c_pok_vc <- challenge<F>;
    z1_pok_vc <- v_c * c_pok_vc + t1_pok_vc;
    z2_pok_vc <- r_vc * c_pok_vc + t2_pok_vc;
    let pok_vc_check = g_evs_d3[0] * z1_pok_vc + h_evs * z2_pok_vc == comm_vc_phase1 * c_pok_vc + alpha_pok_vc;
    verify(pok_vc_check);
    let r_postsc_blind = random<F>;
    let r_eq_p1 = random<F>;
    let derived_blind_p1 = eq_tau_at_rx * (r_prod - r_vc);
    comm_postsc_p1 <- g_evs_d3[0] * e_x + h_evs * r_postsc_blind;
    let comm_derived_p1 = (comm_prod_phase1 - comm_vc_phase1) * eq_tau_at_rx;
    alpha_eq_p1 <- h_evs * r_eq_p1;
    c_eq_p1 <- challenge<F>;
    z_eq_p1 <- c_eq_p1 * (r_postsc_blind - derived_blind_p1) + r_eq_p1;
    let eq_check_p1 = h_evs * z_eq_p1 == (comm_postsc_p1 - comm_derived_p1) * c_eq_p1 + alpha_eq_p1;
    verify(eq_check_p1);

    let ra = challenge<F>;
    let rb = challenge<F>;
    let rc = challenge<F>;
    let t2 = ra * v_a + rb * v_b + rc * v_c;

    let partial_a = eval(mat_a_t, rx);
    let partial_b = eval(mat_b_t, rx);
    let partial_c = eval(mat_c_t, rx);

    let l_mle  = partial_a * ra + partial_b * rb + partial_c * rc;
    let z_mle  = mle(z);
    let m_poly = l_mle * z_mle;

    let pts2   = [i for i in 0..3];
    let cfg2_0 = {{| poly: m_poly, num_variables: {m_lit}, max_degree: 2, round: 0, challenge: zero |}};
    let out2_0 = marginalize(cfg2_0);
    evs2_0 <- out2_0.evaluations;
    verify(t2 == evs2_0[0] + evs2_0[1]);
    let g2_r1     = interpolate(pts2, evs2_0);
    ry0           <- challenge<F>;
    let prev2_vec = eval(g2_r1, [ry0]);
    let prev2     = prev2_vec[0];

    let r_poly_20 = random<F>;
    comm_evs_20 <- dot(g_evs_d2, evs2_0) + h_evs * r_poly_20;
    let r_eval_20 = random<F>;
    comm_eval_20 <- g_evs_d2[0] * prev2 + h_evs * r_eval_20;
    let d_vec_20 = [random<F> for i in 0..3];
    let r_delta_20 = random<F>;
    let r_beta_20  = random<F>;
    delta_20 <- dot(g_evs_d2, d_vec_20) + h_evs * r_delta_20;
    let a_d_dot_20 = dot(d_vec_20, evs2_0);
    beta_20  <- g_evs_d2[0] * a_d_dot_20 + h_evs * r_beta_20;
    c_20     <- challenge<F>;
    z_vec_20   <- [c_20 * evs2_0[i] + d_vec_20[i] for i in 0..3];
    z_delta_20 <- c_20 * r_poly_20 + r_delta_20;
    z_beta_20  <- c_20 * r_eval_20 + r_beta_20;
    let zk_check_20 = dot(g_evs_d2, z_vec_20) + h_evs * z_delta_20 == comm_evs_20 * c_20 + delta_20;
    verify(zk_check_20);

    let sc2 = sc_recurse_d2(out2_0.next_poly, pts2, [ry0], prev2, ry0, 1, g_evs_d2, h_evs);
    let ry  = sc2.challenges;
    let e_y = sc2.final_eval;

    let pcs_z   = ry[0..{nw}];
    let ly_lo   = eq_weights(pcs_z);
    let z_col   = pcs_z[0..{m_h}];
    let z_row   = pcs_z[{m_h}..{nw}];
    let l_vec   = eq_weights(z_row);
    let r_vec   = eq_weights(z_col);

    let big_t   = dot(l_vec, c_rows);
    let r_big_t = dot(l_vec, r_rows);
    let u_vec = [
        dot(l_vec, [w[i*{ncols} + j] for i in 0..{nrows}])
        for j in 0..{ncols}
    ];

    let v_w_val = dot(ly_lo, w);
    sent_v_w    <- v_w_val;

    let r_tau = random<F>;
    tau_pcs <- g_base_w * sent_v_w + h_base_w * r_tau;
    rho_pcs <- challenge<F>;
    let upsilon_pcs = big_t + tau_pcs * rho_pcs;
    let r_upsilon_pcs = r_big_t + r_tau * rho_pcs;
    let a_rho_pcs = [r_vec[j] * rho_pcs for j in 0..{ncols}];
    let y_rho_pcs = sent_v_w * rho_pcs;
    let bullet = bullet_collect(g_base_w, h_base_w, g_vec_w, a_rho_pcs, u_vec, y_rho_pcs, r_upsilon_pcs);
    let b_challenges = bullet.challenges;
    let b_challenges_inv = bullet.challenges_inv;
    let b_Ls = bullet.Ls;
    let b_Rs = bullet.Rs;
    let b_final_y = bullet.final_y;
    let b_final_r = bullet.final_r;
    let s_vec = compute_s_vec(b_challenges, b_challenges_inv);
    let g_hat = dot(g_vec_w, s_vec);
    let a_hat = dot(a_rho_pcs, s_vec);
    let c_sq_vec = [b_challenges[i] * b_challenges[i] for i in 0..{m_h}];
    let c_inv_sq_vec = [b_challenges_inv[i] * b_challenges_inv[i] for i in 0..{m_h}];
    let upsilon_combined = upsilon_pcs + dot(b_Ls, c_sq_vec) + dot(b_Rs, c_inv_sq_vec);
    let d_ipa = random<F>;
    let r_delta_ipa = random<F>;
    let r_beta_ipa = random<F>;
    delta_ipa <- g_hat * d_ipa + h_base_w * r_delta_ipa;
    beta_ipa <- g_base_w * d_ipa + h_base_w * r_beta_ipa;
    c_ipa <- challenge<F>;
    z1_ipa <- d_ipa + c_ipa * b_final_y;
    z2_ipa <- a_hat * (c_ipa * b_final_r + r_beta_ipa) + r_delta_ipa;
    let lhs_ipa = (upsilon_combined * c_ipa + beta_ipa) * a_hat + delta_ipa;
    let rhs_ipa = (g_hat + g_base_w * a_hat) * z1_ipa + h_base_w * z2_ipa;
    let ipa_ok = lhs_ipa == rhs_ipa;

    let io_block = io ++ [one];
    let v_io     = dot(ly_lo, io_block);
    let ry_top   = ry[{m_lit} - 1];
    let v_z      = (one - ry_top) * sent_v_w + ry_top * v_io;

    let v1 = eval(partial_a, ry);
    let v2 = eval(partial_b, ry);
    let v3 = eval(partial_c, ry);

    let r_ey   = random<F>;
    let d_p2   = random<F>;
    let r_d_p2 = random<F>;
    comm_ey_p2 <- g_evs_d2[0] * e_y + h_evs * r_ey;
    alpha_p2   <- g_evs_d2[0] * d_p2 + h_evs * r_d_p2;
    c_p2       <- challenge<F>;
    z1_p2      <- c_p2 * e_y + d_p2;
    z2_p2      <- c_p2 * r_ey + r_d_p2;
    let eq_check_p2 = g_evs_d2[0] * z1_p2 + h_evs * z2_p2 == comm_ey_p2 * c_p2 + alpha_p2;
    verify(eq_check_p2);

    verify(ipa_ok);
    verify(e_y == (ra * v1 + rb * v2 + rc * v3) * v_z)
}}
"#,
        m_lit = m_lit,
        two_m = two_m,
        two_m_vars = two_m_vars,
        nw = nw,
        two_nw = two_nw,
        io_len = io_len,
        m_h = m_h,
        nrows = nrows,
        ncols = ncols,
    )
}

fn main() {
    println!("=========================================");
    println!("ZIPPEL 2^18 COMPILATION TIMING SUITE");
    println!("=========================================");

    let mut timings = Vec::new();
    let target_m = 18;

    // 1. Sumcheck (NUM_VARS_CONST = 18, MAX_DEGREE_CONST = 2)
    let mut sizes_sumcheck = Ctx::new();
    sizes_sumcheck.insert(&Tid::new("NUM_VARS_CONST"), &target_m);
    sizes_sumcheck.insert(&Tid::new("MAX_DEGREE_CONST"), &2);
    let t_sumcheck = compile_protocol::<ArkBls12_381>(
        "Sumcheck (2^18 vars)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/sumcheck/sumcheck.zippel"),
        sizes_sumcheck,
    );
    timings.push(("Sumcheck", t_sumcheck));

    // 2. Bulletproofs (IPA) (S = 18)
    let mut sizes_ipa = Ctx::new();
    sizes_ipa.insert(&Tid::new("S"), &target_m);
    let t_ipa = compile_protocol::<ArkSecp256k1>(
        "Bulletproofs (IPA) (2^18 elements)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/ipa/ipa.zippel"),
        sizes_ipa,
    );
    timings.push(("Bulletproofs (IPA)", t_ipa));

    // 3. KZG (N = 2^18)
    let mut sizes_kzg = Ctx::new();
    sizes_kzg.insert(&Tid::new("N"), &262144);
    let t_kzg = compile_protocol::<ArkBls12_381>(
        "KZG (2^18 coefficients)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/kzg/kzg.zippel"),
        sizes_kzg,
    );
    timings.push(("KZG", t_kzg));

    // 4. Pari (M = 18, N = 1, KMN = 2^18 - 2)
    let mut sizes_pari = Ctx::new();
    sizes_pari.insert(&Tid::new("M"), &target_m);
    sizes_pari.insert(&Tid::new("N"), &1);
    sizes_pari.insert(&Tid::new("KMN"), &262142);
    let t_pari = compile_protocol::<ArkBls12_381>(
        "Pari (2^18 constraints)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/pari/pari.zippel"),
        sizes_pari,
    );
    timings.push(("Pari", t_pari));

    // 5. Groth16 (M = 33, L = 2^18, H = 2^18)
    let mut sizes_groth16 = Ctx::new();
    sizes_groth16.insert(&Tid::new("M"), &33);
    sizes_groth16.insert(&Tid::new("L"), &262144);
    sizes_groth16.insert(&Tid::new("H"), &262144);
    let t_groth16 = compile_protocol::<ArkBls12_381>(
        "Groth16 (2^18 constraints)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/groth16/groth16.zippel"),
        sizes_groth16,
    );
    timings.push(("Groth16", t_groth16));

    // 6. PST13 (N = 18)
    let mut sizes_pst13 = Ctx::new();
    sizes_pst13.insert(&Tid::new("N"), &target_m);
    let t_pst13 = compile_protocol::<ArkBls12_381>(
        "PST13 (2^18 coefficients)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/pst13/pst13.zippel"),
        sizes_pst13,
    );
    timings.push(("PST13", t_pst13));

    // 7. Hyrax (using hyrax_ipa component, S = 18)
    let mut sizes_hyrax = Ctx::new();
    sizes_hyrax.insert(&Tid::new("S"), &target_m);
    let t_hyrax = compile_protocol::<ArkBls12_381>(
        "Hyrax (2^18 elements)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/hyrax_ipa/hyrax_ipa.zippel"),
        sizes_hyrax,
    );
    timings.push(("Hyrax (IPA)", t_hyrax));

    // 8. Spartan (m = 18, generating proto on the fly)
    let proto = generate_proto(target_m);
    let tmp_dir = std::env::temp_dir().join("zippel_spartan_bench");
    std::fs::create_dir_all(&tmp_dir).expect("create tmp dir");
    let spartan_path = tmp_dir.join("spartan_bench_18.zippel");
    std::fs::write(&spartan_path, proto).expect("write generated proto");

    let (_, m_h) = hyrax_split(target_m);
    let mut sizes_spartan = Ctx::new();
    sizes_spartan.insert(&Tid::new("SC"), &target_m);
    sizes_spartan.insert(&Tid::new("S"), &m_h);
    let t_spartan = compile_protocol::<ArkCurve25519>(
        "Spartan (2^18 constraints)",
        spartan_path,
        sizes_spartan,
    );
    timings.push(("Spartan", t_spartan));

    println!("=========================================");
    if let Some(min_t) = timings.iter().min_by(|a, b| a.1.partial_cmp(&b.1).unwrap()) {
        println!("Min time: {} ({:.4}s)", min_t.0, min_t.1);
    }
    if let Some(max_t) = timings.iter().max_by(|a, b| a.1.partial_cmp(&b.1).unwrap()) {
        println!("Max time: {} ({:.4}s)", max_t.0, max_t.1);
    }
    println!("=========================================");
}
