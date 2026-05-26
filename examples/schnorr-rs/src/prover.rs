#![allow(dead_code, unused_imports, unused_variables)]

use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use spongefish::{DuplexSpongeInterface, Encoding, domain_separator, session_id_from_str};

#[derive(Debug)]
pub enum GeneratedError {
    Serialization(ark_serialize::SerializationError),
    Join(tokio::task::JoinError),
    Unimplemented(&'static str),
}

impl From<ark_serialize::SerializationError> for GeneratedError {
    fn from(value: ark_serialize::SerializationError) -> Self {
        Self::Serialization(value)
    }
}

impl From<tokio::task::JoinError> for GeneratedError {
    fn from(value: tokio::task::JoinError) -> Self {
        Self::Join(value)
    }
}

impl std::fmt::Display for GeneratedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Serialization(err) => write!(f, "serialization error: {err}"),
            Self::Join(err) => write!(f, "tokio task join error: {err}"),
            Self::Unimplemented(msg) => write!(f, "generated code scaffold is incomplete: {msg}"),
        }
    }
}

impl std::error::Error for GeneratedError {}

const ZIPPEL_SESSION: &str = "examples/schnorr/schnorr.zippel";

struct InstanceBytes(Vec<u8>);

impl Encoding<[u8]> for InstanceBytes {
    fn encode(&self) -> impl AsRef<[u8]> {
        self.0.as_slice()
    }
}

fn serialize_to_bytes<T: ark_serialize::CanonicalSerialize>(
    value: &T,
) -> Result<Vec<u8>, GeneratedError> {
    let mut out = Vec::new();
    value.serialize_compressed(&mut out)?;
    Ok(out)
}

fn public_message<T: ark_serialize::CanonicalSerialize>(
    state: &mut spongefish::ProverState,
    value: &T,
) -> Result<(), GeneratedError> {
    let bytes = serialize_to_bytes(value)?;
    state.public_message(bytes.as_slice());
    Ok(())
}

fn zippel_state(instance_bytes: Vec<u8>) -> spongefish::ProverState {
    let session = session_id_from_str(ZIPPEL_SESSION);
    let instance = InstanceBytes(instance_bytes);
    domain_separator!("zippel")
        .session(session)
        .instance(&instance)
        .std_prover()
}

fn challenge_scalar(state: &mut spongefish::ProverState) -> ark_bls12_381::Fr {
    use ark_ff::PrimeField;

    let challenge_bytes: [u8; 32] = state.verifier_message();
    let byte_size = (<ark_bls12_381::Fr as PrimeField>::MODULUS_BIT_SIZE as usize).div_ceil(8);
    ark_bls12_381::Fr::from_le_bytes_mod_order(&challenge_bytes[..byte_size.min(32)])
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub u: ark_bls12_381::G1Projective,
    pub z: ark_bls12_381::Fr,
}

#[allow(unused_variables)]
pub async fn prove(
    g: ark_bls12_381::G1Projective,
    h: ark_bls12_381::G1Projective,
    x: ark_bls12_381::Fr,
) -> Result<Proof, GeneratedError> {
    let mut rng = rand::rngs::OsRng;
    let mut instance_bytes = Vec::new();
    instance_bytes.extend(serialize_to_bytes(&g)?);
    instance_bytes.extend(serialize_to_bytes(&h)?);
    let mut state = zippel_state(instance_bytes);
    public_message(&mut state, &g)?;
    public_message(&mut state, &h)?;
    let r = ark_bls12_381::Fr::rand(&mut rng);
    let u = g * r;
    public_message(&mut state, &u)?;
    let c = challenge_scalar(&mut state);
    let z = r + x * c;
    Ok(Proof { u, z })
}
