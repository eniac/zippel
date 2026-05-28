use crate::{Dag, PRef};
use backend::ArkConfig;
#[cfg(test)]
use log::debug;
use spongefish::{Encoding, domain_separator, session_id_from_str};
use std::marker::PhantomData;

#[cfg(test)]
use crate::UDags;
#[cfg(test)]
use backend::ArkBls12_381;
#[cfg(test)]
use lang::ast::UModule;
#[cfg(test)]
use share::Ctx;
#[cfg(test)]
use share::unwrap;

/// Wrapper to make Vec<u8> implement Encoding for use as domain separator instance
struct InstanceBytes(Vec<u8>);

impl Encoding<[u8]> for InstanceBytes {
    fn encode(&self) -> impl AsRef<[u8]> {
        self.0.as_slice()
    }
}

pub struct ZippelDomainSeparator<C: ArkConfig> {
    session: String,
    instance_bytes: Vec<u8>,
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig> ZippelDomainSeparator<C> {
    pub fn new<A>(domsep: &str, _dag: &Dag<C, A>) -> Self {
        Self {
            session: domsep.to_string(),
            instance_bytes: Vec::new(),
            _phantom: PhantomData,
        }
    }

    pub fn new_zippel_domain_seperator<A>(session: &str, dag: &Dag<C, A>) -> Self {
        let mut public_args: Vec<PRef> = dag
            .args()
            .iter()
            .filter(|arg| arg.is_public() && !arg.from_transcript)
            .cloned()
            .collect();

        public_args.sort_by_key(|arg| arg.name().map(|v| v.0.clone()).unwrap_or_default());

        let mut instance_buf = Vec::new();
        for arg in public_args {
            if let Some(vid) = arg.name() {
                let vid_bytes = vid.0.as_bytes();
                instance_buf.extend_from_slice(vid_bytes);

                let type_size = arg.typ.physical_len();
                instance_buf.extend_from_slice(&(type_size as u64).to_le_bytes());
            }
        }

        Self {
            session: session.to_string(),
            instance_bytes: instance_buf,
            _phantom: PhantomData,
        }
    }

    pub fn std_prover(&self) -> spongefish::ProverState {
        let session_bytes = session_id_from_str(&self.session);
        let instance = InstanceBytes(self.instance_bytes.clone());
        domain_separator!("zippel")
            .session(session_bytes)
            .instance(&instance)
            .std_prover()
    }
}

#[test]
fn test_domain_separator() {
    let ex = r#"
    proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
        let r = random<F>;
        u <- g*r;
        c <- challenge<F>;
        z <- r + x*c;
        verify(g*z == u + h*c)
    }
"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let domain_seperator = ZippelDomainSeparator::new("test_domain_separator", &gs[0]);
    let _prover = domain_seperator.std_prover();
    debug!("Domain Seperator created successfully");
}
