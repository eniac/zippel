
#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum RTyp {
    Index,
    Scalar,
    G1,
    G2,
    GT,
    VecG1(usize),
    VecG2(usize),
    VecGT(usize)
}

