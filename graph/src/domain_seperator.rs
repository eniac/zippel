use ark_ec::{
    CurveGroup,
    pairing::{Pairing, PairingOutput},
};
use ark_serialize::CanonicalSerialize;
use backend::{ABase, ATyp, ArkBls12_381, ArkConfig};
use lang::ast::UModule;
use petgraph::graph::Node;
use share::unwrap;
use spongefish::{
    ByteDomainSeparator, DefaultHash, DomainSeparator, DuplexSpongeInterface,
    codecs::arkworks_algebra::{FieldDomainSeparator, GroupDomainSeparator},
};

use crate::{Dag, UDags, domain_seperator};

/// Extend the domain separator with the Schnorr protocol.
trait ZippelDomainSeparator<C: ArkConfig, A> {
    /// Shortcut: create a new schnorr proof with statement + proof.
    fn new_zippel_domain_seperator(domsep: &str, dag: &Dag<C, A>) -> Self;

    /// Add the Schnorr protocol to the domain separator.
    fn from_dag(self, dag: &Dag<C, A>) -> Self;
    fn from_transcript_node(self, node: &crate::Node<C, A>, label: usize) -> Self;
    fn from_input_node(self, node: &crate::Node<C, A>) -> Self;
    fn from_atyp(self, typ: ATyp) -> Self;
}

impl<H, C, A> ZippelDomainSeparator<C, A> for DomainSeparator<H>
where
    H: DuplexSpongeInterface,
    C: ArkConfig,
{
    fn new_zippel_domain_seperator(domsep: &str, dag: &Dag<C, A>) -> Self {
        Self::new(domsep).from_dag(dag)
    }

    fn from_input_node(mut self, node: &crate::Node<C, A>) -> Self {
        match &node {
            crate::Node::Inp(c, prefs) => {
                for pref in prefs.clone() {
                    self = <spongefish::DomainSeparator<H> as domain_seperator::ZippelDomainSeparator<C, A>>::from_atyp(self,pref.typ);
                }
            }
            _ => {
                panic!("Not an input node")
            }
        }
        self
    }

    fn from_transcript_node(mut self, node: &crate::Node<C, A>, label: usize) -> Self {
        match &node {
            crate::Node::Transcr(c, _) => match c {
                crate::Op::Challenge(c_typ, _) => {
                    self =
                        self.add_bytes(C::F::default().compressed_size(), &format!("chall{}", label));
                }
                _ => {
                    let typ: ATyp = c.typ();
                    self = <spongefish::DomainSeparator<H> as domain_seperator::ZippelDomainSeparator<C, A>>::from_atyp(self,typ);
                }
            },
            _ => {
                panic!("Not a transcript node")
            }
        }
        self
    }

    fn from_atyp(mut self, typ: ATyp) -> Self {
        match typ {
            ATyp::Base(base) => match base {
                ABase::G1 => {
                    self = self.add_bytes(C::G1::default().compressed_size(), "G1");
                }
                ABase::G2 => {
                    self = self.add_bytes(C::G2::default().compressed_size(), "G2");
                }
                ABase::GT => {
                    todo!()
                }
                ABase::Scalar => {
                    self = self.add_bytes(C::F::default().compressed_size(), "F");
                }
                _ => {
                    panic!("Cannot add this base element to transcript");
                }
            },
            ATyp::Vec(another_typ, size) => {
                self = self.add_bytes(
                    C::F::default().compressed_size() * size,
                    &format!("Vec-{}", size),
                );
                for _ in 0..size {
                    self =
                    <spongefish::DomainSeparator<H> as domain_seperator::ZippelDomainSeparator<
                        C,
                        A,
                    >>::from_atyp(self, *another_typ.clone());
                }
            }
            _ => {
                panic!("Cannot add this type to transcript");
            }
        }
        self
    }

    fn from_dag(mut self, dag: &Dag<C, A>) -> Self {
        self = self.from_input_node(&dag.0[dag.input_node()]);
        for transcript_node_index in dag.transcript_nodes() {
            self = self
                .from_transcript_node(&dag.0[transcript_node_index], transcript_node_index.index());
        }
        self.clone()
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
        verify(g*z == u + h*c);
    }
"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let domain_seperator = DomainSeparator::<DefaultHash>::new_zippel_domain_seperator(
        "test_domain_separator",
        &gs[0],
    );
    println!("Domain Seperator: {:?}", domain_seperator);
}
