//! Transcript and challenge code generation support.

/// Return helper Rust source for the given session identifier.
///
/// The source includes a `ZIPPEL_SESSION` constant, serialization helpers,
/// a spongefish prover-state factory, and a scalar-challenge helper.  None
/// of the emitted text references Zippel-internal crates (`backend`,
/// `graph`, `runtime`).
pub(crate) fn helper_source(session: &str) -> String {
    format!(
        r#"const ZIPPEL_SESSION: &str = {session:?};

struct InstanceBytes(Vec<u8>);

fn serialize_to_bytes<T: ark_serialize::CanonicalSerialize>(
    value: &T,
) -> Result<Vec<u8>, GeneratedError> {{
    let mut out = Vec::new();
    value.serialize_compressed(&mut out)?;
    Ok(out)
}}

fn public_message<T: ark_serialize::CanonicalSerialize>(
    value: &T,
) -> Result<Vec<u8>, GeneratedError> {{
    serialize_to_bytes(value)
}}

fn zippel_state(instance_bytes: Vec<u8>) -> spongefish::ProverState {{
    let _ = instance_bytes;
    let io = spongefish::IOPattern::new(ZIPPEL_SESSION);
    io.to_prover_state()
}}

fn challenge_scalar(state: &mut spongefish::ProverState) -> ark_bls12_381::Fr {{
    use ark_ff::PrimeField;

    let mut bytes = [0u8; 64];
    state.fill_challenge_bytes(&mut bytes).expect("challenge bytes");
    let bit_size = (<ark_bls12_381::Fr as PrimeField>::MODULUS_BIT_SIZE as usize).div_ceil(8);
    ark_bls12_381::Fr::from_le_bytes_mod_order(&bytes[..bit_size.min(64)])
}}
"#
    )
}
