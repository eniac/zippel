use thiserror::Error;

pub type Result<T> = std::result::Result<T, CompilerError>;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("unsupported Graph IR node {node}: {detail}")]
    UnsupportedNode { node: usize, detail: String },

    #[error("unsupported Graph IR op at node {node}: {op}")]
    UnsupportedOp { node: usize, op: String },

    #[error("unsupported Graph IR type at node {node}: {typ}")]
    UnsupportedType { node: usize, typ: String },

    #[error("graph is not acyclic; topological planning stopped at node {node}")]
    CyclicGraph { node: usize },

    #[error("missing generated variable for dependency node {node}")]
    MissingDependency { node: usize },

    #[error("verifier graph does not contain a supported check node")]
    MissingVerifierCheck,

    #[error("generated source I/O failed")]
    Io(#[from] std::io::Error),
}
