//! Node construction and manipulation tests

#[cfg(test)]
mod node_tests {
    use crate::{Node, Op, Ref, mk};
    use backend::{ArkBls12_381 as C, ATyp};
    use crate::tests::test_helpers::*;
    use lang::id::Vid;
    use lang::typ::Nothing;
    use petgraph::graph::NodeIndex;
    
    #[test]
    fn test_node_is_op_true() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), Nothing);
        assert!(node.is_op());
    }
    
    #[test]
    fn test_node_is_op_false_inp() {
        let node = Node::<C, Nothing>::Inp(Vid::from("test"), vec![]);
        assert!(!node.is_op());
    }
    
    #[test]
    fn test_node_is_input_true() {
        let node = Node::<C, Nothing>::Inp(Vid::from("test"), vec![]);
        assert!(node.is_input());
    }
    
    #[test]
    fn test_node_is_input_false() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), Nothing);
        assert!(!node.is_input());
    }
    
    #[test]
    fn test_node_is_relation_true() {
        let node = Node::<C, Nothing>::Rel(Vid::from("rel"), vec![]);
        assert!(node.is_relation());
    }
    
    #[test]
    fn test_node_is_relation_false() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), Nothing);
        assert!(!node.is_relation());
    }
    
    #[test]
    fn test_node_is_verifier_check_true() {
        let op = Op::<C, Ref>::check(Op::value(&scalar::<C>(1)));
        let _node = Node::<C, Nothing>::Rel(Vid::from("check"), vec![]);
        // Note: is_verifier_check requires Op node with Check op
        let check_node = Node::Op(mk::<C>(op), Nothing);
        assert!(check_node.is_verifier_check());
    }
    
    #[test]
    fn test_node_is_transcript_false_default() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), Nothing);
        assert!(!node.is_transcript());
    }
    
    #[test]
    fn test_node_set_and_query_transcript() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let mut node = Node::Op(mk::<C>(op), Nothing);
        
        assert!(!node.is_transcript());
        node.set_transcript();
        assert!(node.is_transcript());
    }
    
    #[test]
    fn test_node_into_op_success() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op.clone()), Nothing);
        
        let extracted = node.into_op();
        match &*extracted {
            Op::Value(_) => (), // Success
            _ => panic!("Should extract Op successfully"),
        }
    }
    
    #[test]
    fn test_node_op_extraction_none() {
        let node = Node::<C, Nothing>::Inp(Vid::from("test"), vec![]);
        let extracted = node.op();
        assert!(extracted.is_none());
    }
    
    #[test]
    fn test_node_references_op() {
        let ref1 = Ref::Node(NodeIndex::new(1));
        let ref2 = Ref::Node(NodeIndex::new(2));
        
        let op = Op::<C, Ref>::add(
            Op::reference(ref1.clone(), ATyp::scalar()),
            Op::reference(ref2.clone(), ATyp::scalar()),
            ATyp::scalar(),
        );
        
        let node = Node::Op(mk::<C>(op), Nothing);
        let refs = node.references();
        
        assert_eq!(refs.len(), 2);
        assert!(refs.contains(&ref1));
        assert!(refs.contains(&ref2));
    }
    
    #[test]
    fn test_node_references_inp() {
        let node = Node::<C, Nothing>::Inp(Vid::from("test"), vec![]);
        let refs = node.references();
        assert_eq!(refs.len(), 0);
    }
    
    #[test]
    fn test_node_map_node_indices() {
        let ref1 = Ref::Node(NodeIndex::new(1));
        let op = Op::<C, Ref>::reference(ref1, ATyp::scalar());
        let node = Node::Op(mk::<C>(op), Nothing);
        
        let mapped = node.map_node_indices(&|idx| NodeIndex::new(idx.index() + 10));
        
        // Verify mapping occurred
        let refs = mapped.references();
        assert_eq!(refs.len(), 1);
        assert_eq!(refs[0].node(), NodeIndex::new(11));
    }
    
    #[test]
    fn test_node_name_with_vid() {
        let vid = Vid::from("my_var");
        let node = Node::<C, Nothing>::Inp(vid.clone(), vec![]);
        
        let name = node.name();
        assert_eq!(name, Some(&vid));
    }
    
    #[test]
    fn test_node_name_without_vid() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), Nothing);
        
        let name = node.name();
        assert_eq!(name, None);
    }
    
    #[test]
    fn test_node_add_annotation() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), Nothing);
        
        let annotated = node.add_annotation(String::from("new_annotation"));
        match annotated {
            Node::Op(_, (Nothing, ann)) => assert_eq!(ann, String::from("new_annotation")),
            _ => panic!("Should add annotation"),
        }
    }
    
    #[test]
    fn test_node_drop_annotation() {
        let op = Op::<C, Ref>::value(&scalar::<C>(42));
        let node = Node::Op(mk::<C>(op), String::from("my_annotation"));
        
        let dropped = node.drop_annotation();
        match dropped {
            Node::Op(_, Nothing) => (), // Annotation dropped
            _ => panic!("Should drop annotation"),
        }
    }
}
