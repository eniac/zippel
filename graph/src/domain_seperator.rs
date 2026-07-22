use crate::{ArgKind, Dag, Node};
use backend::ArkConfig;
use lang::id::Vid;
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
        // Collect instance, non-transcript Arg nodes sorted by name.
        let mut instance_args: Vec<(&Vid, &backend::ATyp)> = dag
            .input_args()
            .into_iter()
            .filter_map(|n| match &dag[n] {
                Node::Arg(name, typ, qual, _, ArgKind::Input) => {
                    if qual.is_instance() {
                        Some((name, typ))
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect();

        instance_args.sort_by_key(|(name, _)| name.0.as_str());

        let mut instance_buf = Vec::new();
        for (vid, typ) in instance_args {
            let vid_bytes = vid.0.as_bytes();
            instance_buf.extend_from_slice(vid_bytes);

            let type_size = typ.physical_len();
            instance_buf.extend_from_slice(&(type_size as u64).to_le_bytes());
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
    proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
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
