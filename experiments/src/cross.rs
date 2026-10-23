//! Cross-verification against native baselines (see `docs/CROSS_VERIFY_PLAN.md`).
//!
//! Cross-tests supply the same seeded [`Challenges`] sequence to both
//! implementations. Zippel accepts it as a [`Challenger`], and Spartan accepts it
//! through its native `ProofTranscript` traits. Other vendored transcripts draw
//! from `Challenges::default()` under `cfg(test)`. Benchmarks and Spartan's
//! ordinary native tests keep their real Fiat–Shamir transcripts. These fixed
//! challenges check proof arithmetic and conversion, not transcript binding.

use backend::{Backend, Field, Value};
use lang::id::Tid;
use rand::{RngCore, SeedableRng, rngs::StdRng};
use share::Ctx;
use std::path::PathBuf;
use zippel::runtime::Challenger;
use zippel::{CompileOptions, CompiledProver, CompiledVerifier, ParsedModule};

impl<G: ark_ec::CurveGroup> crate::ark_spartan_upstream::transcript::ProofTranscript<G>
    for Challenges
{
    fn append_message(&mut self, _: &'static [u8], _: &[u8]) {}

    fn challenge_scalar(&mut self, _: &'static [u8]) -> G::ScalarField {
        self.next_scalar()
    }
}

impl crate::libspartan_upstream::transcript::ProofTranscript for Challenges {
    fn append_message(&mut self, _: &'static [u8], _: &[u8]) {}

    fn challenge_scalar(&mut self, _: &'static [u8]) -> crate::libspartan_upstream::scalar::Scalar {
        crate::libspartan_upstream::scalar::Scalar::from_bytes_wide(&self.next_bytes())
    }
}

/// Which implementation produces the proof in a cross-verification test.
#[derive(Clone, Copy)]
pub enum Direction {
    /// The native prover produces a proof for Zippel's verifier.
    NativeToZippel,
    /// Zippel's prover produces a proof for the native verifier.
    ZippelToNative,
}

/// `examples/<name>/<name>.zippel`, compiled at `sizes` and projected.
///
/// # Panics
/// If the example fails to load, compile or project.
pub fn compile<C: Backend>(
    name: &str,
    sizes: &[(&str, usize)],
) -> (CompiledProver<C>, CompiledVerifier<C>) {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("../examples/{name}/{name}.zippel"));
    let mut ctx = Ctx::new();
    for (name, size) in sizes {
        ctx.insert(&Tid::new(name), size);
    }
    let protocol = ParsedModule::load(&path)
        .expect("parse protocol")
        .compile::<C>(&ctx, CompileOptions::default())
        .expect("compile protocol");
    (
        protocol.project_prover(),
        protocol.project_verifier().expect("project verifier"),
    )
}

/// A seeded challenge sequence. Each challenge is 64 bytes reduced modulo the field
/// order, so every field implementation gets the same element.
#[derive(Clone)]
pub struct Challenges(StdRng);

impl Challenges {
    /// The sequence for `seed`.
    #[must_use]
    pub fn seeded(seed: u64) -> Self {
        Self(StdRng::seed_from_u64(seed))
    }

    /// The bytes of the next challenge.
    #[must_use]
    pub fn next_bytes(&mut self) -> [u8; 64] {
        let mut bytes = [0; 64];
        self.0.fill_bytes(&mut bytes);
        bytes
    }

    /// The next challenge, in an arkworks field.
    pub fn next_scalar<F: ark_ff::PrimeField>(&mut self) -> F {
        F::from_le_bytes_mod_order(&self.next_bytes())
    }
}

/// The sequence the vendored transcripts draw from.
impl Default for Challenges {
    fn default() -> Self {
        Self::seeded(0)
    }
}

/// Zippel's absorbed values are ignored: the challenges are fixed.
impl<C: Backend> Challenger<C> for Challenges {
    fn instance(&mut self, _: &Value<C>) {}

    fn message(&mut self, _: &Value<C>) {}

    fn challenge(&mut self) -> Value<C> {
        Value::Scalar(C::F::from_le_bytes_mod_order(&self.next_bytes()))
    }
}

/// For natives that take their sponge as a parameter (arkworks'
/// `CryptographicSponge`): absorbs are ignored, and field elements are the sequence.
impl ark_crypto_primitives::sponge::CryptographicSponge for Challenges {
    type Config = ();

    fn new((): &()) -> Self {
        Self::default()
    }

    fn absorb(&mut self, _: &impl ark_crypto_primitives::sponge::Absorb) {}

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        let mut bytes = vec![0; num_bytes];
        self.0.fill_bytes(&mut bytes);
        bytes
    }

    fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
        let bytes = self.squeeze_bytes(num_bits.div_ceil(8));
        (0..num_bits)
            .map(|i| bytes[i / 8] >> (i % 8) & 1 == 1)
            .collect()
    }

    fn squeeze_field_elements<F: ark_ff::PrimeField>(&mut self, num_elements: usize) -> Vec<F> {
        (0..num_elements).map(|_| self.next_scalar()).collect()
    }
}
