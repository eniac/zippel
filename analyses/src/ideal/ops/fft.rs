//! `Op::Fft`, `Op::Ifft`, and DFT `Op::Evaluate` encoders.

use ark_ff::{FftField, Field};

use backend::ArkConfig;
use backend::op::HasOpFactory;

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;
use super::dft_row;
use super::link_to_polys;

/// `Op::Ifft(v)`: p = ifft(v) — inverse DFT. The coefficient form `var`
/// is the IDFT of the evaluation form `a`. Each coefficient is:
///   p[j] = (1/N) · Σ_i ω^{-i·j} · v[i]
/// where ω is a primitive N-th root of unity. The type checker
/// guarantees N is a 2-adic divisor of |F|-1, so ω always exists.
pub fn encode_ifft<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &graph::GOp<C>,
) {
    let v_polys = PolySource::ref_vars(a, &ctx.ideal.vars);
    let n = v_polys.len();
    let omega = C::F::get_root_of_unity(n as u64)
        .expect("IFFT size must have a root of unity; type checker guarantees this");
    let omega_inv = omega.inverse().unwrap();
    let n_inv = C::F::from(n as u64).inverse().unwrap();
    let polys: Vec<Polynomial<C::F>> = (0..n)
        .map(|j| &dft_row::<C>(&v_polys, omega_inv, j) * &Polynomial::lit(&n_inv))
        .collect();
    link_to_polys(ctx.ideal, var, polys);
}

/// `Op::Fft(p)`: v = fft(p) — forward DFT. Each evaluation is:
///   v[i] = Σ_j ω^{i·j} · p[j]
/// The type checker guarantees N is a 2-adic divisor of |F|-1.
pub fn encode_fft<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &graph::GOp<C>,
) {
    let coeff_polys = PolySource::ref_vars(a, &ctx.ideal.vars);
    let n = coeff_polys.len();
    let omega = C::F::get_root_of_unity(n as u64)
        .expect("FFT size must have a root of unity; type checker guarantees this");
    let polys: Vec<Polynomial<C::F>> = (0..n)
        .map(|i| dft_row::<C>(&coeff_polys, omega, i))
        .collect();
    link_to_polys(ctx.ideal, var, polys);
}

/// `Op::Evaluate(p, None, None)`: DFT evaluation on the full grid.
/// Each evaluation point is `v[i] = Σ_j ω^{i·j} · p[j]`.
/// The type checker guarantees N is a 2-adic divisor of |F|-1.
pub fn encode_dft<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    p: &graph::GOp<C>,
) {
    let coeff_polys = PolySource::ref_vars(p, &ctx.ideal.vars);
    let n = coeff_polys.len();
    let omega = C::F::get_root_of_unity(n as u64)
        .expect("Evaluate grid size must have a root of unity; type checker guarantees this");
    let polys: Vec<Polynomial<C::F>> = (0..n)
        .map(|i| dft_row::<C>(&coeff_polys, omega, i))
        .collect();
    link_to_polys(ctx.ideal, var, polys);
}
