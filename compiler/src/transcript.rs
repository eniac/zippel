//! Transcript and challenge code generation support.

use crate::options::RustTarget;

/// Return helper Rust source for the given session identifier.
///
/// The source includes a `ZIPPEL_SESSION` constant, serialization helpers,
/// a spongefish prover-state factory, and a scalar-challenge helper.  None
/// of the emitted text references Zippel-internal crates (`backend`,
/// `graph`, `runtime`).
pub(crate) fn helper_source(session: &str, target: &RustTarget) -> String {
    let scalar_type = target.scalar_type;
    format!(
        r#"const ZIPPEL_SESSION: &str = {session:?};

struct InstanceBytes(Vec<u8>);

impl Encoding<[u8]> for InstanceBytes {{
    fn encode(&self) -> impl AsRef<[u8]> {{
        self.0.as_slice()
    }}
}}

fn serialize_to_bytes<T: ark_serialize::CanonicalSerialize>(
    value: &T,
) -> Result<Vec<u8>, GeneratedError> {{
    let mut out = Vec::new();
    value.serialize_compressed(&mut out)?;
    Ok(out)
}}

fn public_message<T: ark_serialize::CanonicalSerialize>(
    state: &mut spongefish::ProverState,
    value: &T,
) -> Result<(), GeneratedError> {{
    let bytes = serialize_to_bytes(value)?;
    state.public_message(bytes.as_slice());
    Ok(())
}}

fn zippel_state(instance_bytes: Vec<u8>) -> spongefish::ProverState {{
    let session = session_id_from_str(ZIPPEL_SESSION);
    let instance = InstanceBytes(instance_bytes);
    domain_separator!("zippel")
        .session(session)
        .instance(&instance)
        .std_prover()
}}

fn challenge_scalar(state: &mut spongefish::ProverState) -> {scalar_type} {{
    use ark_ff::PrimeField;

    let challenge_bytes: [u8; 32] = state.verifier_message();
    let byte_size = (<{scalar_type} as PrimeField>::MODULUS_BIT_SIZE as usize).div_ceil(8);
    {scalar_type}::from_le_bytes_mod_order(&challenge_bytes[..byte_size.min(32)])
}}
"#
    )
}
