use rand::Rng;
use rayon::prelude::*;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

use ark_ec::VariableBaseMSM;
use ark_ec::bls12::Bls12;
use ark_ec::mnt4::MNT4;
use ark_ec::models::bn::Bn;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::scalar_mul::ScalarMul;
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{AdditiveGroup, Fp64, MontBackend, MontConfig, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::UniformRand;

use crate::nothing::{NoCurve, NoPairing};
use crate::op::{HasOpFactory, OpFactory};
use std::sync::RwLock;

/// API to Arkworks finite fields, elliptic curves, and pairings
pub trait ArkConfig:
    Clone + Copy + Send + Sync + 'static + Eq + PartialEq + Ord + PartialOrd + fmt::Display + Hash
{
    /// Scalar field of the backend; every Zippel `Scalar` value lives here.
    type F: PrimeField;
    /// First source group of the pairing, in projective coordinates.
    type G1: CurveGroup<ScalarField = Self::F, Affine = Self::G1Affine>;
    /// Second source group of the pairing; equal to `G1` for pairing-free curves.
    type G2: CurveGroup<ScalarField = Self::F, Affine = Self::G2Affine>;
    /// Affine representation of `G1`, used as the `MulBase` for MSM and batch scalar mul.
    type G1Affine: AffineRepr<ScalarField = Self::F, Group = Self::G1>;
    /// Affine representation of `G2`.
    type G2Affine: AffineRepr<ScalarField = Self::F, Group = Self::G2>;
    /// Pairing engine tying `G1`, `G2` and the target group together.
    type P: Pairing<ScalarField = Self::F, G1 = Self::G1, G2 = Self::G2>;
    /// Target group of the pairing; defaults to `PairingOutput<Self::P>`.
    type GT = PairingOutput<Self::P>;

    /// Scalar-field operation bundle used by the runtime evaluator.
    type FOps: ArkScalarOps<Self::F>;
    /// `G1` operation bundle (group add, scalar mul, MSM).
    type G1Ops: ArkGroupOps<Self::G1>;
    /// `G2` operation bundle; identical to `G1Ops` for pairing-free curves.
    type G2Ops: ArkGroupOps<Self::G2>;
    /// Pairing operation bundle (bilinear map and target-group arithmetic).
    type POps: ArkPairingOps<Self::P>;
}

/// Operations on Arkworks scalar fields
pub trait ArkScalarOps<F: PrimeField> {
    /// Additive identity of the scalar field.
    #[inline]
    fn zero() -> F {
        F::zero()
    }

    /// Multiplicative identity of the scalar field.
    #[inline]
    fn one() -> F {
        F::one()
    }

    /// Embeds a machine-sized index into the scalar field, going through `u64`.
    ///
    /// Used to lift Zippel literals and loop indices into field elements.
    #[inline]
    fn from_usize(i: usize) -> F {
        F::from(i as u64)
    }

    /// Scalar addition, saves result in f2
    #[inline]
    fn add(f1: &F, f2: &mut F) {
        *f2 += f1
    }

    /// Scalar negation in place
    #[inline]
    fn neg(f: &mut F) {
        f.neg_in_place();
    }

    /// Scalar subtraction, saves result in f2
    #[inline]
    fn sub(f1: &F, f2: &mut F) {
        Self::neg(f2);
        Self::add(f1, f2);
    }

    /// Scalar multiplication, saves result in f2
    #[inline]
    fn mul(f1: &F, f2: &mut F) {
        *f2 *= f1
    }

    /// Scalar inversion in place.
    #[inline]
    fn inv(f: &mut F) {
        f.inverse_in_place();
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn div(f1: &F, f2: &mut F) {
        Self::inv(f2);
        Self::mul(f1, f2);
    }

    /// Scalar exponentiation, saves result in f1
    #[inline]
    fn pow(f1: &mut F, i: u64) {
        if i == 0 {
            *f1 = F::one();
            return;
        }
        let mut i = i;
        while i.is_multiple_of(2) {
            f1.square_in_place();
            i /= 2;
        }
        *f1 = f1.pow([i])
    }

    /// Pointwise vector addition, saving the result in `f2`.
    ///
    /// Runs in parallel via `rayon`; only the first `min(len)` entries are touched.
    #[inline]
    fn vec_add(f1: &Vec<F>, f2: &mut Vec<F>) {
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a += b);
    }

    /// Pointwise vector negation in place.
    #[inline]
    fn vec_neg(f: &mut Vec<F>) {
        f.par_iter_mut().for_each(|x| {
            x.neg_in_place();
        });
    }

    /// Pointwise vector subtraction, saving the result in `f2`.
    #[inline]
    fn vec_sub(f1: &Vec<F>, f2: &mut Vec<F>) {
        Self::vec_neg(f2);
        Self::vec_add(f1, f2);
    }

    /// Pointwise (Hadamard) vector multiplication, saving the result in `f2`.
    #[inline]
    fn vec_mul(f1: &Vec<F>, f2: &mut Vec<F>) {
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a *= b);
    }

    /// Inner product of two scalar vectors, computed as a parallel sum of products.
    #[inline]
    fn vec_dot(f1: &Vec<F>, f2: &Vec<F>) -> F {
        f1.par_iter()
            .zip(f2.par_iter())
            .map(|(a, b)| *a * *b)
            .reduce(|| Self::zero(), |acc, x| acc + x)
    }

    /// Vector batch inversion, saves result in f2
    #[inline]
    fn vec_inv(f: &mut Vec<F>) {
        ark_ff::fields::batch_inversion::<F>(f);
    }

    /// Pointwise vector division, saving the result in `f2`.
    ///
    /// Computes `f2 := f1 / f2` via a single batch inversion, mirroring the
    /// scalar [`div`](ArkScalarOps::div) contract.
    #[inline]
    fn vec_div(f1: &Vec<F>, f2: &mut Vec<F>) {
        Self::vec_inv(f2);
        Self::vec_mul(f1, f2);
    }

    /// Raises every entry of `f1` to the `i`-th power in place.
    ///
    /// Squares out the factors of two first, then finishes with a windowed `pow`.
    #[inline]
    fn vec_pow(f1: &mut Vec<F>, i: u64) {
        f1.par_iter_mut().for_each(|x| {
            let mut i = i;
            while i.is_multiple_of(2) {
                x.square_in_place();
                i /= 2;
            }
            *x = x.pow([i]);
        });
    }

    /// FFT and IFFT
    /// Inverse FFT in place, converting evaluations on the domain to coefficients.
    ///
    /// # Panics
    ///
    /// Panics if no `GeneralEvaluationDomain` exists for `a.len()`, i.e. the
    /// length is not a supported FFT domain size for this field.
    #[inline]
    fn vec_ifft(a: &mut Vec<F>) {
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        domain.ifft_in_place(a);
    }

    /// Forward FFT in place, turning coefficients into evaluations on the domain.
    ///
    /// # Panics
    ///
    /// Panics if no `GeneralEvaluationDomain` exists for `a.len()`.
    #[inline]
    fn vec_fft(a: &mut Vec<F>) {
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        domain.fft_in_place(a);
    }

    /// Random and challenge sponge infrastructure
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> F {
        F::rand(rng)
    }

    /// Squeezes a Fiat-Shamir challenge out of the transcript sponge.
    ///
    /// Reads 32 sponge bytes and reduces the modulus-sized prefix mod `p`, so the
    /// prover and verifier derive identical `Op::Challenge` values.
    fn challenge<H: DuplexSpongeInterface<U = u8>>(state: &mut ProverState<H>) -> F {
        let byte_size = (F::MODULUS_BIT_SIZE as usize).div_ceil(8);
        let challenge_bytes: [u8; 32] = state.verifier_message();
        F::from_le_bytes_mod_order(&challenge_bytes[..byte_size.min(32)])
    }

    /// Samples a vector of `n` independent uniform scalars.
    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<F> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut().for_each(|x| *x = Self::rand(rng));
        v
    }

    /// Formats a scalar through the arkworks `Display` impl.
    ///
    /// # Errors
    ///
    /// Returns `fmt::Error` if the underlying formatter fails.
    #[inline]
    fn write(f: &F, h: &mut fmt::Formatter) -> fmt::Result {
        write!(h, "{}", f)
    }
}

/// Operations on Arkworks elliptic-curve groups.
///
/// One instance is selected per `ArkConfig` for `G1` and for `G2`; the runtime
/// evaluator dispatches every group-typed `Op` through this trait.
pub trait ArkGroupOps<G: CurveGroup> {
    /// Group constants
    #[inline]
    fn zero() -> G {
        G::ZERO
    }
    /// Fixed generator of the group, used to lift scalars into group elements.
    #[inline]
    fn generator() -> G {
        G::generator()
    }
    /// Group operations
    #[inline]
    fn add(g1: &G::Affine, g2: &mut G) {
        *g2 += g1;
    }
    /// Group negation in place.
    #[inline]
    fn neg(g: &mut G) {
        g.neg_in_place();
    }
    /// Group subtraction, saving the result in `g2`.
    #[inline]
    fn sub(g1: &G::Affine, g2: &mut G) {
        Self::neg(g2);
        Self::add(g1, g2);
    }
    /// Scalar multiplication of a group element, saving the result in `g`.
    #[inline]
    fn mul(f: &G::Scalar, g: &mut G) {
        *g *= f;
    }
    /// Samples a uniformly random group element.
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> G {
        G::rand(rng)
    }

    /// Samples a vector of `n` independent uniformly random group elements.
    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<G> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut().for_each(|x| *x = Self::rand(rng));
        v
    }

    /// Group vec operations
    #[inline]
    fn vec_mul(g: &G, f: &[G::Scalar]) -> Vec<G::MulBase> {
        // batch_mul builds a window-sized precomputed table whose construction
        // costs ~85 modular inversions on BLS12-381 G1 — fine when amortized
        // over many scalars, but ~85x wasted work for a single one. Single
        // Group * Scalar ops in zippel route through here too, so special-case.
        if f.len() == 1 {
            vec![(*g * f[0]).into_affine()]
        } else {
            g.batch_mul(f)
        }
    }
    /// Multi-scalar multiplication, i.e. the group analogue of an inner product.
    ///
    /// # Panics
    ///
    /// Panics if `g` and `f` have different lengths, which arkworks' `msm`
    /// rejects; equal lengths are a shape invariant established by typing.
    #[inline]
    fn vec_dot(g: &[G::MulBase], f: &[G::Scalar]) -> G {
        G::msm(g, f).unwrap()
    }
    /// Formats a group element through the arkworks `Display` impl.
    ///
    /// # Errors
    ///
    /// Returns `fmt::Error` if the underlying formatter fails.
    #[inline]
    fn write(g: &G, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
}

/// Operations on the pairing target group `GT` and the bilinear map itself.
///
/// Selected as `ArkConfig::POps`; pairing-free curves use the `NoPairing` stub.
pub trait ArkPairingOps<P: Pairing> {
    /// Group constants
    #[inline]
    fn zero() -> PairingOutput<P> {
        PairingOutput::ZERO
    }
    /// Fixed generator of the target group.
    #[inline]
    fn generator() -> PairingOutput<P> {
        PairingOutput::generator()
    }
    /// Group operations
    #[inline]
    fn add(g1: &PairingOutput<P>, g2: &mut PairingOutput<P>) {
        *g2 += g1;
    }
    /// Target-group negation in place.
    #[inline]
    fn neg(g: &mut PairingOutput<P>) {
        g.neg_in_place();
    }
    /// Target-group subtraction, saving the result in `g2`.
    #[inline]
    fn sub(g1: &PairingOutput<P>, g2: &mut PairingOutput<P>) {
        Self::neg(g2);
        Self::add(g1, g2);
    }
    /// Scalar multiplication of a target-group element, saving the result in `g`.
    #[inline]
    fn mul(f: &<PairingOutput<P> as AdditiveGroup>::Scalar, g: &mut PairingOutput<P>) {
        *g *= f;
    }
    /// Samples a uniformly random target-group element.
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> PairingOutput<P> {
        PairingOutput::rand(rng)
    }

    /// Samples a vector of `n` independent uniformly random target-group elements.
    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<PairingOutput<P>> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut().for_each(|x| *x = Self::rand(rng));
        v
    }

    /// Group vec operations
    #[inline]
    fn vec_mul(g: &PairingOutput<P>, f: &[P::ScalarField]) -> Vec<PairingOutput<P>> {
        if f.len() == 1 {
            vec![*g * f[0]]
        } else {
            g.batch_mul(f)
        }
    }
    /// Multi-scalar multiplication in the target group.
    ///
    /// # Panics
    ///
    /// Panics if `g` and `f` have different lengths, which arkworks' `msm` rejects.
    #[inline]
    fn vec_dot(g: &[PairingOutput<P>], f: &[P::ScalarField]) -> PairingOutput<P> {
        // TODO: What does Err<usize> mean here?
        <PairingOutput<P> as VariableBaseMSM>::msm(g, f).unwrap()
    }
    /// Formats a target-group element through the arkworks `Display` impl.
    ///
    /// # Errors
    ///
    /// Returns `fmt::Error` if the underlying formatter fails.
    #[inline]
    fn write(g: &PairingOutput<P>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }

    /// Pairing operations
    #[inline]
    fn billinear_map(g1: &P::G1, g2: &P::G2) -> PairingOutput<P> {
        P::pairing(*g1, *g2)
    }

    /// Pointwise bilinear map over two equal-length group vectors.
    ///
    /// Unlike `billinear_vec_dot` this keeps the pairs separate instead of summing.
    #[inline]
    fn billinear_vec_mul(g1: &Vec<P::G1>, g2: &Vec<P::G2>) -> Vec<PairingOutput<P>> {
        g1.par_iter()
            .zip(g2.par_iter())
            .map(|(g1, g2)| Self::billinear_map(g1, g2))
            .collect()
    }

    /// Σᵢ e(g1ᵢ, g2ᵢ) via a single `multi_miller_loop + final_exponentiation`.
    /// One final exp instead of N. Replaces the previous per-pair `pairing()`
    /// fold, which paid N final exps to compute a sum that ends up equal to
    /// `multi_pairing` by definition (`Σᵢ e(...)` is exactly what the latter
    /// returns). The verifier's pairing check goes through this path via the
    /// `dot(VecG1, VecG2) -> GT` arm in `value_dot`.
    #[inline]
    fn billinear_vec_dot(g1: &[P::G1], g2: &[P::G2]) -> PairingOutput<P> {
        P::multi_pairing(g1.iter().copied(), g2.iter().copied())
    }
}

/// Zippel arkworks configuration helper objects
pub struct ArkScalarConfig<F: PrimeField>(PhantomData<F>);
impl<F: PrimeField> ArkScalarOps<F> for ArkScalarConfig<F> {}

/// Nullary carrier for the group operation bundle of a backend.
pub struct ArkGroupConfig<G: CurveGroup>(PhantomData<G>);
impl<G: CurveGroup> ArkGroupOps<G> for ArkGroupConfig<G> {}

/// Nullary carrier for the pairing operation bundle of a backend.
pub struct ArkPairingConfig<P: Pairing>(PhantomData<P>);
impl<P: Pairing> ArkPairingOps<P> for ArkPairingConfig<P> {}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Zero;

    type BlsPairing = <ArkBls12_381 as ArkConfig>::P;
    type BlsPairingOps = <ArkBls12_381 as ArkConfig>::POps;

    #[test]
    fn billinear_vec_dot_matches_pairing_fold_reference() {
        let g1_base = <ArkBls12_381 as ArkConfig>::G1::generator();
        let g2_base = <ArkBls12_381 as ArkConfig>::G2::generator();

        for len in [1usize, 2, 4] {
            let g1: Vec<_> = (0..len)
                .map(|i| g1_base * <ArkBls12_381 as ArkConfig>::F::from((i + 2) as u64))
                .collect();
            let g2: Vec<_> = (0..len)
                .map(|i| g2_base * <ArkBls12_381 as ArkConfig>::F::from((i + 3) as u64))
                .collect();

            let batched = BlsPairingOps::billinear_vec_dot(&g1, &g2);
            let reference = g1
                .iter()
                .zip(g2.iter())
                .fold(PairingOutput::<BlsPairing>::zero(), |acc, (g1, g2)| {
                    acc + BlsPairing::pairing(*g1, *g2)
                });

            assert_eq!(batched, reference);
        }
    }

    #[test]
    fn billinear_vec_dot_implementation_uses_multi_pairing_source_guard() {
        let source = include_str!("config.rs");
        let billinear_vec_dot_impl = source
            .split("fn billinear_vec_dot")
            .nth(1)
            .and_then(|tail| tail.split("/// Zippel arkworks configuration").next())
            .expect("billinear_vec_dot implementation should be present");

        assert!(
            billinear_vec_dot_impl.contains("P::multi_pairing"),
            "billinear_vec_dot must use P::multi_pairing to batch final exponentiation"
        );
        assert!(
            !billinear_vec_dot_impl.contains("P::pairing("),
            "billinear_vec_dot must not regress to per-element P::pairing calls"
        );
    }
}

/// Concrete Zippel arkworks configurations
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkBls12_381 {}

/// `BN254` pairing-friendly backend, the curve used by most Ethereum tooling.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkBn254 {}

/// `MNT4-298` pairing-friendly backend, a cycle-friendly curve for recursion.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkMNT4_298 {}

/// Curve25519 backend; a prime-order Edwards group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkCurve25519 {}

/// `secp256k1` backend; a prime-order Weierstrass group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkSecp256k1 {}

/// Pallas backend, the first half of the Pasta cycle; no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkPallas {}

/// Vesta backend, the second half of the Pasta cycle; no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkVesta {}

/// Ed25519 backend; a prime-order Edwards group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkEd25519 {}

/// Field-only backend over an arbitrary `PrimeField`, with `NoCurve`/`NoPairing`
/// stubs for the group and target-group slots.
///
/// Used for tiny-modulus tests where group arithmetic is irrelevant.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkFieldN<F: PrimeField>(PhantomData<F>);

/// Field-only backend over the 17-element prime field; used in small unit tests.
pub type ArkField17 = ArkFieldN<F17>;
/// Field-only backend over the 65537-element prime field; used in small unit tests.
pub type ArkField65537 = ArkFieldN<F65537>;

impl fmt::Display for ArkBls12_381 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BLS12-381")
    }
}
impl fmt::Display for ArkBn254 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BN254")
    }
}
impl fmt::Display for ArkMNT4_298 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "MNT4-298")
    }
}
impl fmt::Display for ArkCurve25519 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Curve25519")
    }
}
impl fmt::Display for ArkSecp256k1 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SECP256K1")
    }
}

impl fmt::Display for ArkPallas {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Pallas")
    }
}
impl fmt::Display for ArkVesta {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Vesta")
    }
}
impl fmt::Display for ArkEd25519 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ed25519")
    }
}
impl<F: PrimeField> fmt::Display for ArkFieldN<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Field<{}>", F::MODULUS)
    }
}

impl ArkConfig for ArkBls12_381 {
    type F = ark_bls12_381::Fr;
    type G1 = ark_bls12_381::G1Projective;
    type G2 = ark_bls12_381::G2Projective;
    type G1Affine = ark_bls12_381::G1Affine;
    type G2Affine = ark_bls12_381::G2Affine;
    type P = Bls12<ark_bls12_381::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkBn254 {
    type F = ark_bn254::Fr;
    type G1 = ark_bn254::G1Projective;
    type G2 = ark_bn254::G2Projective;
    type G1Affine = ark_bn254::G1Affine;
    type G2Affine = ark_bn254::G2Affine;
    type P = Bn<ark_bn254::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkMNT4_298 {
    type F = ark_mnt4_298::Fr;
    type G1 = ark_mnt4_298::G1Projective;
    type G2 = ark_mnt4_298::G2Projective;
    type G1Affine = ark_mnt4_298::G1Affine;
    type G2Affine = ark_mnt4_298::G2Affine;
    type P = MNT4<ark_mnt4_298::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkCurve25519 {
    type F = ark_curve25519::Fr;
    type G1 = ark_curve25519::EdwardsProjective;
    type G2 = ark_curve25519::EdwardsProjective;
    type G1Affine = ark_curve25519::EdwardsAffine;
    type G2Affine = ark_curve25519::EdwardsAffine;
    type P = NoPairing<ark_curve25519::EdwardsProjective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkSecp256k1 {
    type F = ark_secp256k1::Fr;
    type G1 = ark_secp256k1::Projective;
    type G2 = ark_secp256k1::Projective;
    type G1Affine = ark_secp256k1::Affine;
    type G2Affine = ark_secp256k1::Affine;
    type P = NoPairing<ark_secp256k1::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkPallas {
    type F = ark_pallas::Fr;
    type G1 = ark_pallas::Projective;
    type G2 = ark_pallas::Projective;
    type G1Affine = ark_pallas::Affine;
    type G2Affine = ark_pallas::Affine;
    type P = NoPairing<ark_pallas::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkVesta {
    type F = ark_vesta::Fr;
    type G1 = ark_vesta::Projective;
    type G2 = ark_vesta::Projective;
    type G1Affine = ark_vesta::Affine;
    type G2Affine = ark_vesta::Affine;
    type P = NoPairing<ark_vesta::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkEd25519 {
    type F = ark_ed25519::Fr;
    type G1 = ark_ed25519::EdwardsProjective;
    type G2 = ark_ed25519::EdwardsProjective;
    type G1Affine = ark_ed25519::EdwardsAffine;
    type G2Affine = ark_ed25519::EdwardsAffine;
    type P = NoPairing<ark_ed25519::EdwardsProjective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl<F: PrimeField> ArkConfig for ArkFieldN<F> {
    type F = F;
    type G1 = NoCurve<F>;
    type G2 = NoCurve<F>;
    type G1Affine = NoCurve<F>;
    type G2Affine = NoCurve<F>;
    type P = NoPairing<NoCurve<F>>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

/// Montgomery parameters for the 17-element prime field (modulus 17, generator 3).
#[derive(MontConfig, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
/// Arkworks Montgomery backend instantiated with `F17Config` over one 64-bit limb.
pub type Mont17 = MontBackend<F17Config, 1>;

/// The 17-element prime field, the smallest field used by backend unit tests.
pub type F17 = Fp64<Mont17>;

/// Montgomery parameters for the 65537-element prime field (modulus 65537,
/// generator 3).
///
/// 65536 is a power of two, so this field admits radix-2 FFT domains up to
/// size 65536, unlike `F17Config`.
#[derive(MontConfig, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[modulus = "65537"]
#[generator = "3"]
pub struct F65537Config;
/// Arkworks Montgomery backend instantiated with `F65537Config` over one 64-bit limb.
pub type Mont65537 = MontBackend<F65537Config, 1>;
/// The 65537-element prime field, used where FFT-capable test domains are needed.
pub type F65537 = Fp64<Mont65537>;

/// Takes as input a struct, and converts them to a series of bytes. All traits
/// that implement `CanonicalSerialize` can be automatically converted to bytes
/// in this manner.
#[macro_export]
macro_rules! to_bytes {
    ($x:expr) => {{
        let mut buf = ark_std::vec![];
        ark_serialize::CanonicalSerialize::serialize_compressed($x, &mut buf).map(|_| buf)
    }};
}

/// Macro to implement HasOpFactory for a concrete ArkConfig type.
/// Creates a lazy_static RwLock<OpFactory<T>> and wires it up via the trait.
macro_rules! impl_op_factory {
    ($config:ty, $factory_name:ident) => {
        lazy_static::lazy_static! {
            static ref $factory_name: RwLock<OpFactory<$config>> =
                RwLock::new(hashconsing::HConsign::empty());
        }
        impl HasOpFactory for $config {
            fn op_factory() -> &'static RwLock<OpFactory<Self>> {
                &$factory_name
            }
        }
    };
}

impl_op_factory!(ArkBls12_381, BLS381_OP_FACTORY);
impl_op_factory!(ArkBn254, BN254_OP_FACTORY);
impl_op_factory!(ArkMNT4_298, MNT4_OP_FACTORY);
impl_op_factory!(ArkCurve25519, CURVE25519_OP_FACTORY);
impl_op_factory!(ArkSecp256k1, SECP256K1_OP_FACTORY);
impl_op_factory!(ArkPallas, PALLAS_OP_FACTORY);
impl_op_factory!(ArkVesta, VESTA_OP_FACTORY);
impl_op_factory!(ArkEd25519, ED25519_OP_FACTORY);
impl_op_factory!(ArkField17, FIELD17_OP_FACTORY);
impl_op_factory!(ArkField65537, FIELD65537_OP_FACTORY);
