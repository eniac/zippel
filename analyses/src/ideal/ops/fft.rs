//! `Op::Fft`, `Op::Ifft`, and DFT `Op::Evaluate` encoders.

use crate::AnalysisBackend;
use ark_ff::{FftField, Field};

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;
use super::dft_row;
use super::link_to_polys;

/// `Op::Ifft(v)`: p = ifft(v) — inverse DFT. The coefficient form `var`
/// is the IDFT of the evaluation form `a`. Each coefficient is:
///   p[j] = (1/N) · Σ_i ω^{-i·j} · v[i]
/// where ω is a primitive N-th root of unity. N is a power of two (the type
/// checker) within the field's 2-adicity (`Dag::check_backend`), so ω exists.
pub fn ifft_op<C: AnalysisBackend>(ctx: &mut EncodeCtx<'_, C>, var: &Var, a: &graph::GOp<C>) {
    let v_polys = PolySource::ref_vars(a, &ctx.ideal.vars);
    let n = v_polys.len();
    let omega = C::F::get_root_of_unity(n as u64)
        .expect("compilation rejects FFTs larger than the field's domain");
    let omega_inv = omega.inverse().unwrap();
    let n_inv = C::F::from(n as u64).inverse().unwrap();
    let polys: Vec<Polynomial<C::F>> = (0..n)
        .map(|j| &dft_row::<C>(&v_polys, omega_inv, j) * &Polynomial::lit(&n_inv))
        .collect();
    link_to_polys(ctx.ideal, var, polys);
}

/// `Op::Fft(p)`: v = fft(p) — forward DFT. Each evaluation is:
///   v[i] = Σ_j ω^{i·j} · p[j]
/// N is a power of two within the field's 2-adicity, as for `ifft_op`.
pub fn fft_op<C: AnalysisBackend>(ctx: &mut EncodeCtx<'_, C>, var: &Var, a: &graph::GOp<C>) {
    let coeff_polys = PolySource::ref_vars(a, &ctx.ideal.vars);
    let n = coeff_polys.len();
    let omega = C::F::get_root_of_unity(n as u64)
        .expect("compilation rejects FFTs larger than the field's domain");
    let polys: Vec<Polynomial<C::F>> = (0..n)
        .map(|i| dft_row::<C>(&coeff_polys, omega, i))
        .collect();
    link_to_polys(ctx.ideal, var, polys);
}
