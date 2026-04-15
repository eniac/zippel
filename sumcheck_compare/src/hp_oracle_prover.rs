// Vendored from EspressoSystems/hyperplonk `subroutines/src/poly_iop/sum_check/prover.rs` (MIT).
// Runs sum-check prover rounds with explicit verifier challenges (no Merlin transcript).

use std::sync::Arc;

use hp_ark_ff::{batch_inversion, Field, One, Zero};
use arithmetic::{fix_variables, VirtualPolynomial};
use hp_ark_bls12_381::Fr as F;
use hp_ark_poly::DenseMultilinearExtension;

pub struct HpSumcheckOracle {
    round: usize,
    poly: VirtualPolynomial<F>,
    extrapolation_aux: Vec<(Vec<F>, Vec<F>)>,
    challenges: Vec<F>,
}

impl HpSumcheckOracle {
    pub fn init(poly: &VirtualPolynomial<F>) -> Result<Self, String> {
        if poly.aux_info.num_variables == 0 {
            return Err("sum-check: num_variables == 0".into());
        }
        let extrapolation_aux = (1..poly.aux_info.max_degree)
            .map(|degree| {
                let points = (0..=degree as u64).map(F::from).collect::<Vec<_>>();
                let weights = barycentric_weights(&points);
                (points, weights)
            })
            .collect::<Vec<_>>();
        Ok(Self {
            round: 0,
            poly: poly.clone(),
            extrapolation_aux,
            challenges: Vec::new(),
        })
    }

    /// One sum-check round. Pass `None` for the first round only; then `Some(r_i)` for each
    /// subsequent round (same order as HyperPlonk `IOPProverState::prove_round_and_update_state`).
    pub fn prove_round(&mut self, challenge: Option<F>) -> Result<Vec<F>, String> {
        let nv = self.poly.aux_info.num_variables;
        if self.round >= nv {
            return Err("sum-check: prover inactive".into());
        }

        let mut flattened: Vec<DenseMultilinearExtension<F>> = self
            .poly
            .flattened_ml_extensions
            .iter()
            .map(|x| x.as_ref().clone())
            .collect();

        if let Some(chal) = challenge {
            if self.round == 0 {
                return Err("sum-check: first round must use challenge None".into());
            }
            self.challenges.push(chal);
            let r = self.challenges[self.round - 1];
            for mle in &mut flattened {
                *mle = fix_variables(mle, &[r]);
            }
        } else if self.round > 0 {
            return Err("sum-check: verifier message missing".into());
        }

        self.round += 1;

        let products_list = self.poly.products.clone();
        let mut products_sum = vec![F::zero(); self.poly.aux_info.max_degree + 1];

        for (coefficient, products) in products_list.iter() {
            let k = products.len();
            let n_loops = 1usize << (nv - self.round);
            let mut coeff_acc = vec![F::zero(); k + 1];

            for b in 0..n_loops {
                let mut buf: Vec<(F, F)> = products
                    .iter()
                    .map(|&idx| {
                        let table = &flattened[idx];
                        (table[b << 1], table[(b << 1) + 1] - table[b << 1])
                    })
                    .collect();

                coeff_acc[0] += buf.iter().map(|(e, _)| *e).product::<F>();
                for j in 1..=k {
                    for (eval, step) in buf.iter_mut() {
                        *eval += *step;
                    }
                    coeff_acc[j] += buf.iter().map(|(e, _)| *e).product::<F>();
                }
            }

            for s in coeff_acc.iter_mut() {
                *s *= *coefficient;
            }

            let extrapolation: Vec<F> = (0..self.poly.aux_info.max_degree.saturating_sub(k))
                .map(|i| {
                    let (points, weights) = &self.extrapolation_aux[k - 1];
                    let at = F::from((k + 1 + i) as u64);
                    extrapolate(points, weights, &coeff_acc, &at)
                })
                .collect();

            for (ps, v) in products_sum
                .iter_mut()
                .zip(coeff_acc.iter().chain(extrapolation.iter()))
            {
                *ps += *v;
            }
        }

        self.poly.flattened_ml_extensions = flattened.into_iter().map(Arc::new).collect();

        Ok(products_sum)
    }
}

fn barycentric_weights(points: &[F]) -> Vec<F> {
    let mut weights = points
        .iter()
        .enumerate()
        .map(|(j, point_j)| {
            points
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != j)
                .map(|(_, point_i)| *point_j - point_i)
                .reduce(|acc, value| acc * value)
                .unwrap_or_else(F::one)
        })
        .collect::<Vec<_>>();
    batch_inversion(&mut weights);
    weights
}

fn extrapolate(points: &[F], weights: &[F], evals: &[F], at: &F) -> F {
    let mut coeffs: Vec<F> = points.iter().map(|point| *at - point).collect();
    batch_inversion(&mut coeffs);
    coeffs
        .iter_mut()
        .zip(weights)
        .for_each(|(coeff, weight)| *coeff *= weight);
    let sum_inv = coeffs.iter().sum::<F>().inverse().unwrap_or_default();
    coeffs
        .iter()
        .zip(evals)
        .map(|(coeff, eval)| *coeff * eval)
        .sum::<F>()
        * sum_inv
}
