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
use std::collections::{HashMap, HashSet};
use petgraph::graph::{NodeIndex};
use crate::{Dag, UDags, domain_seperator};

/// Extend the domain separator with the Schnorr protocol.
pub struct ZippelDomainSeparator<H: DuplexSpongeInterface> (
    pub DomainSeparator<H>
);

impl<H> ZippelDomainSeparator<H>
where
    H: DuplexSpongeInterface
{
    pub fn new_zippel_domain_seperator<C: ArkConfig, A>(domsep: &str, dag: &Dag<C, A>) -> Self {
        Self(DomainSeparator::<H>::new(domsep)).from_dag(dag)
    }

    pub fn from_input_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>) -> Self {
        
        let mut size: usize = 0;
        match &node {
            crate::Node::Inp(c, prefs) => {
                for pref in prefs.clone() {
                    if pref.qualifier.is_public() {
                        self = Self::from_atyp::<C>(self,pref.typ);
                    }
                }
            }
            _ => {
                panic!("Not an input node")
            }
        }
        self
    }

    pub fn from_challenge_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>, label: usize) -> Self {
        match &node {
            crate::Node::Transcr(c, _) => match c {
                crate::Op::Challenge(typ, _) => {
                    self = Self(self.0.squeeze(
                        C::F::default().compressed_size(),
                        &format!("chall{}", label),
                    ));

                },
                _ => {}
            },
            _ => {

            }
        }
        self
    }

    pub fn from_transcript_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>, label: usize) -> Self {
        match &node {
            crate::Node::Transcr(c, _) => {
                let typ: ATyp = c.typ();
                self = Self::from_atyp::<C>(self,typ);
            },
            _ => {
                panic!("Not a transcript node")
            }
        }
        self
    }

    pub fn from_atyp<C: ArkConfig>(mut self, typ: ATyp) -> Self {
        match typ {
            ATyp::Base(base) => match base {
                ABase::G1 => {
                    self = Self(self.0.add_bytes(C::G1::default().compressed_size(), "G1"));
                }
                ABase::G2 => {
                    self = Self(self.0.add_bytes(C::G2::default().compressed_size(), "G2"));
                }
                ABase::GT => {
                    self = Self(self.0.add_bytes(C::G2::default().compressed_size(), "GT"));
                }
                ABase::Scalar => {
                    self = Self(self.0.add_bytes(C::F::default().compressed_size(), "F"));
                }
                _ => {
                    panic!("Cannot add this base element to transcript");
                }
            },
            ATyp::Vec(another_typ, size) => {
                for _ in 0..size {
                    self =
                    Self::from_atyp::<C>(self, *another_typ.clone());
                }
            }
            _ => {
                panic!("Cannot add this type to transcript");
            }
        }
        self
    }

    pub fn from_dag<C: ArkConfig, A>(mut self, dag: &Dag<C, A>) -> Self {
        let input_node_index = dag.input_node();
        let node = &dag.0[input_node_index];
        self = self.from_input_node(&node);

        let transcript_nodes = dag.transcript_nodes();
       
        if !transcript_nodes.is_empty() {
            let mut parent_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
            let mut has_parent_in_list = HashSet::new();
            
            for &node in &transcript_nodes {
                for parent in dag.neighbors_directed(node, petgraph::Direction::Incoming) {
                    if transcript_nodes.contains(&parent) {
                        parent_map.insert(node, parent);
                        has_parent_in_list.insert(node);
                    }
                }
            }        

            let mut ordered = Vec::new();
            let root = transcript_nodes.iter()
                .find(|&&n| !has_parent_in_list.contains(&n))
                .expect("Cycle detected in transcript nodes");
            
            let mut current = *root;
            ordered.push(current);
            while let Some(&child) = transcript_nodes.iter()
                .find(|&&n| parent_map.get(&n) == Some(&current)) {
                ordered.push(child);
                current = child;
            }
            for transcript_node_index in ordered {
                self = self.from_challenge_node(&dag.0[transcript_node_index], transcript_node_index.index());
                self = self
                    .from_transcript_node(&dag.0[transcript_node_index], transcript_node_index.index());
            }  
        }      

        
        Self(self.0.clone())
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
    let domain_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(
        "test_domain_separator",
        &gs[0],
    );
    println!("Domain Seperator: {:?}", domain_seperator.0);
}
