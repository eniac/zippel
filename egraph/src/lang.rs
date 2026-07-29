//! ZIR and RIR e-graph languages, analyses, and cost functions.
//!
//! See `docs/egraph-plan.md` (implementation plan) and
//! `docs/egraph-design-log.md` (design rationale) for details.

use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::marker::PhantomData;

use egg::{Analysis, CostFunction, DidMerge, EGraph, Id, Language, Symbol};

use backend::{ATyp, ArkConfig, Value};
use lang::ast::BinOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

// =====================================================================
// ZIR — the analysis/optimization IR
// =====================================================================

/// The ZIR e-graph language. See `docs/egraph-design-log.md` §3.2.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum ZIR<C: ArkConfig> {
    // ---- leaves ----
    Var(Symbol),
    Constant(Value<C>),
    // ---- binary arithmetic ----
    Add([Id; 2]),
    Sub([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),
    Rem([Id; 2]),
    Pow([Id; 2]),
    Dot([Id; 2]),
    Concat([Id; 2]),
    Neg([Id; 1]),
    // ---- crypto ----
    Pair([Id; 2]),
    Random(Symbol, bool),
    Challenge(Symbol, bool),
    Log(Symbol, [Id; 1]),
    // ---- polynomial shape ops ----
    Poly([Id; 1]),
    Coef([Id; 1]),
    Mle([Id; 1]),
    Fft([Id; 1]),
    Ifft([Id; 1]),
    Interpolate([Id; 2]),
    Evaluate([Id; 2]),
    EvaluateGrid([Id; 1]),
    EvaluateSelected([Id; 3]),
    // ---- structural ----
    Ram([Id; 2]),
    Vec(Box<[Id]>),
    Record(Box<[Symbol]>, Box<[Id]>),
    Proj(Symbol, [Id; 1]),
    // ---- loops ----
    Map(Symbol, [Id; 2]),
    Reduce(BinOp, [Id; 1]),
    // ---- control / side-effects ----
    Seq([Id; 2]),
    Assert([Id; 2]),
    Verify([Id; 2]),
}

/// Discriminant for ZIR — variant tag only (no C parameter).
/// Used by egg for short-circuiting hashconsing lookups.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ZIRDiscriminant {
    Var,
    Constant,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Dot,
    Concat,
    Neg,
    Pair,
    Random,
    Challenge,
    Log,
    Poly,
    Coef,
    Mle,
    Fft,
    Ifft,
    Interpolate,
    Evaluate,
    EvaluateGrid,
    EvaluateSelected,
    Ram,
    Vec,
    Record,
    Proj,
    Map,
    Reduce,
    Seq,
    Assert,
    Verify,
}

impl<C: ArkConfig + std::fmt::Debug> Language for ZIR<C> {
    type Discriminant = ZIRDiscriminant;

    fn discriminant(&self) -> Self::Discriminant {
        match self {
            ZIR::Var(_) => ZIRDiscriminant::Var,
            ZIR::Constant(_) => ZIRDiscriminant::Constant,
            ZIR::Add(_) => ZIRDiscriminant::Add,
            ZIR::Sub(_) => ZIRDiscriminant::Sub,
            ZIR::Mul(_) => ZIRDiscriminant::Mul,
            ZIR::Div(_) => ZIRDiscriminant::Div,
            ZIR::Rem(_) => ZIRDiscriminant::Rem,
            ZIR::Pow(_) => ZIRDiscriminant::Pow,
            ZIR::Dot(_) => ZIRDiscriminant::Dot,
            ZIR::Concat(_) => ZIRDiscriminant::Concat,
            ZIR::Neg(_) => ZIRDiscriminant::Neg,
            ZIR::Pair(_) => ZIRDiscriminant::Pair,
            ZIR::Random(_, _) => ZIRDiscriminant::Random,
            ZIR::Challenge(_, _) => ZIRDiscriminant::Challenge,
            ZIR::Log(_, _) => ZIRDiscriminant::Log,
            ZIR::Poly(_) => ZIRDiscriminant::Poly,
            ZIR::Coef(_) => ZIRDiscriminant::Coef,
            ZIR::Mle(_) => ZIRDiscriminant::Mle,
            ZIR::Fft(_) => ZIRDiscriminant::Fft,
            ZIR::Ifft(_) => ZIRDiscriminant::Ifft,
            ZIR::Interpolate(_) => ZIRDiscriminant::Interpolate,
            ZIR::Evaluate(_) => ZIRDiscriminant::Evaluate,
            ZIR::EvaluateGrid(_) => ZIRDiscriminant::EvaluateGrid,
            ZIR::EvaluateSelected(_) => ZIRDiscriminant::EvaluateSelected,
            ZIR::Ram(_) => ZIRDiscriminant::Ram,
            ZIR::Vec(_) => ZIRDiscriminant::Vec,
            ZIR::Record(_, _) => ZIRDiscriminant::Record,
            ZIR::Proj(_, _) => ZIRDiscriminant::Proj,
            ZIR::Map(_, _) => ZIRDiscriminant::Map,
            ZIR::Reduce(_, _) => ZIRDiscriminant::Reduce,
            ZIR::Seq(_) => ZIRDiscriminant::Seq,
            ZIR::Assert(_) => ZIRDiscriminant::Assert,
            ZIR::Verify(_) => ZIRDiscriminant::Verify,
        }
    }

    fn matches(&self, other: &Self) -> bool {
        // Compare variant + data fields, NOT children Ids.
        match (self, other) {
            (ZIR::Var(a), ZIR::Var(b)) => a == b,
            (ZIR::Constant(a), ZIR::Constant(b)) => a == b,
            (ZIR::Add(_), ZIR::Add(_))
            | (ZIR::Sub(_), ZIR::Sub(_))
            | (ZIR::Mul(_), ZIR::Mul(_))
            | (ZIR::Div(_), ZIR::Div(_))
            | (ZIR::Rem(_), ZIR::Rem(_))
            | (ZIR::Pow(_), ZIR::Pow(_))
            | (ZIR::Dot(_), ZIR::Dot(_))
            | (ZIR::Concat(_), ZIR::Concat(_))
            | (ZIR::Neg(_), ZIR::Neg(_))
            | (ZIR::Pair(_), ZIR::Pair(_))
            | (ZIR::Poly(_), ZIR::Poly(_))
            | (ZIR::Coef(_), ZIR::Coef(_))
            | (ZIR::Mle(_), ZIR::Mle(_))
            | (ZIR::Fft(_), ZIR::Fft(_))
            | (ZIR::Ifft(_), ZIR::Ifft(_))
            | (ZIR::Interpolate(_), ZIR::Interpolate(_))
            | (ZIR::Evaluate(_), ZIR::Evaluate(_))
            | (ZIR::EvaluateGrid(_), ZIR::EvaluateGrid(_))
            | (ZIR::EvaluateSelected(_), ZIR::EvaluateSelected(_))
            | (ZIR::Ram(_), ZIR::Ram(_))
            | (ZIR::Seq(_), ZIR::Seq(_))
            | (ZIR::Assert(_), ZIR::Assert(_))
            | (ZIR::Verify(_), ZIR::Verify(_)) => true,
            (ZIR::Random(a, na), ZIR::Random(b, nb)) => a == b && na == nb,
            (ZIR::Challenge(a, na), ZIR::Challenge(b, nb)) => a == b && na == nb,
            (ZIR::Log(a, _), ZIR::Log(b, _)) => a == b,
            (ZIR::Record(an, _), ZIR::Record(bn, _)) => an == bn,
            (ZIR::Proj(a, _), ZIR::Proj(b, _)) => a == b,
            (ZIR::Map(a, _), ZIR::Map(b, _)) => a == b,
            (ZIR::Reduce(a, _), ZIR::Reduce(b, _)) => a == b,
            (ZIR::Vec(a), ZIR::Vec(b)) => a.len() == b.len(),
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            ZIR::Var(_) | ZIR::Constant(_) | ZIR::Random(_, _) | ZIR::Challenge(_, _) => &[],
            ZIR::Add(ids)
            | ZIR::Sub(ids)
            | ZIR::Mul(ids)
            | ZIR::Div(ids)
            | ZIR::Rem(ids)
            | ZIR::Pow(ids)
            | ZIR::Dot(ids)
            | ZIR::Concat(ids)
            | ZIR::Pair(ids)
            | ZIR::Interpolate(ids)
            | ZIR::Evaluate(ids)
            | ZIR::Ram(ids)
            | ZIR::Seq(ids)
            | ZIR::Assert(ids)
            | ZIR::Verify(ids) => ids.as_slice(),
            ZIR::Neg(ids)
            | ZIR::Poly(ids)
            | ZIR::Coef(ids)
            | ZIR::Mle(ids)
            | ZIR::Fft(ids)
            | ZIR::Ifft(ids)
            | ZIR::EvaluateGrid(ids)
            | ZIR::Log(_, ids)
            | ZIR::Proj(_, ids)
            | ZIR::Reduce(_, ids) => ids.as_slice(),
            ZIR::EvaluateSelected(ids) => ids.as_slice(),
            ZIR::Map(_, ids) => ids.as_slice(),
            ZIR::Vec(ids) => ids,
            ZIR::Record(_, ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            ZIR::Var(_) | ZIR::Constant(_) | ZIR::Random(_, _) | ZIR::Challenge(_, _) => &mut [],
            ZIR::Add(ids)
            | ZIR::Sub(ids)
            | ZIR::Mul(ids)
            | ZIR::Div(ids)
            | ZIR::Rem(ids)
            | ZIR::Pow(ids)
            | ZIR::Dot(ids)
            | ZIR::Concat(ids)
            | ZIR::Pair(ids)
            | ZIR::Interpolate(ids)
            | ZIR::Evaluate(ids)
            | ZIR::Ram(ids)
            | ZIR::Seq(ids)
            | ZIR::Assert(ids)
            | ZIR::Verify(ids) => ids.as_mut_slice(),
            ZIR::Neg(ids)
            | ZIR::Poly(ids)
            | ZIR::Coef(ids)
            | ZIR::Mle(ids)
            | ZIR::Fft(ids)
            | ZIR::Ifft(ids)
            | ZIR::EvaluateGrid(ids)
            | ZIR::Log(_, ids)
            | ZIR::Proj(_, ids)
            | ZIR::Reduce(_, ids) => ids.as_mut_slice(),
            ZIR::EvaluateSelected(ids) => ids.as_mut_slice(),
            ZIR::Map(_, ids) => ids.as_mut_slice(),
            ZIR::Vec(ids) => ids,
            ZIR::Record(_, ids) => ids,
        }
    }
}

// Manual Ord — needed by Language trait. Compares by discriminant first,
// then by data fields.
impl<C: ArkConfig + std::fmt::Debug> PartialOrd for ZIR<C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<C: ArkConfig + std::fmt::Debug> Ord for ZIR<C> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare discriminants first (by variant order in the enum)
        let d1 = self.discriminant();
        let d2 = other.discriminant();
        let d_cmp = discriminant_cmp(&d1, &d2);
        if d_cmp != Ordering::Equal {
            return d_cmp;
        }
        // Same variant — compare data fields (not children)
        match (self, other) {
            (ZIR::Var(a), ZIR::Var(b)) => a.cmp(b),
            (ZIR::Constant(a), ZIR::Constant(b)) => a.cmp(b),
            (ZIR::Add(a), ZIR::Add(b)) => a.cmp(b),
            (ZIR::Sub(a), ZIR::Sub(b)) => a.cmp(b),
            (ZIR::Mul(a), ZIR::Mul(b)) => a.cmp(b),
            (ZIR::Div(a), ZIR::Div(b)) => a.cmp(b),
            (ZIR::Rem(a), ZIR::Rem(b)) => a.cmp(b),
            (ZIR::Pow(a), ZIR::Pow(b)) => a.cmp(b),
            (ZIR::Dot(a), ZIR::Dot(b)) => a.cmp(b),
            (ZIR::Concat(a), ZIR::Concat(b)) => a.cmp(b),
            (ZIR::Neg(a), ZIR::Neg(b)) => a.cmp(b),
            (ZIR::Pair(a), ZIR::Pair(b)) => a.cmp(b),
            (ZIR::Random(a, na), ZIR::Random(b, nb)) => a.cmp(b).then(na.cmp(nb)),
            (ZIR::Challenge(a, na), ZIR::Challenge(b, nb)) => a.cmp(b).then(na.cmp(nb)),
            (ZIR::Log(a, _), ZIR::Log(b, _)) => a.cmp(b),
            (ZIR::Poly(a), ZIR::Poly(b)) => a.cmp(b),
            (ZIR::Coef(a), ZIR::Coef(b)) => a.cmp(b),
            (ZIR::Mle(a), ZIR::Mle(b)) => a.cmp(b),
            (ZIR::Fft(a), ZIR::Fft(b)) => a.cmp(b),
            (ZIR::Ifft(a), ZIR::Ifft(b)) => a.cmp(b),
            (ZIR::Interpolate(a), ZIR::Interpolate(b)) => a.cmp(b),
            (ZIR::Evaluate(a), ZIR::Evaluate(b)) => a.cmp(b),
            (ZIR::EvaluateGrid(a), ZIR::EvaluateGrid(b)) => a.cmp(b),
            (ZIR::EvaluateSelected(a), ZIR::EvaluateSelected(b)) => a.cmp(b),
            (ZIR::Ram(a), ZIR::Ram(b)) => a.cmp(b),
            (ZIR::Vec(a), ZIR::Vec(b)) => a.cmp(b),
            (ZIR::Record(an, _), ZIR::Record(bn, _)) => an.cmp(bn),
            (ZIR::Proj(a, _), ZIR::Proj(b, _)) => a.cmp(b),
            (ZIR::Map(a, _), ZIR::Map(b, _)) => a.cmp(b),
            (ZIR::Reduce(a, _), ZIR::Reduce(b, _)) => a.cmp(b),
            (ZIR::Seq(a), ZIR::Seq(b)) => a.cmp(b),
            (ZIR::Assert(a), ZIR::Assert(b)) => a.cmp(b),
            (ZIR::Verify(a), ZIR::Verify(b)) => a.cmp(b),
            // Different variants with same discriminant is impossible
            _ => Ordering::Equal,
        }
    }
}

/// Total order for ZIRDiscriminant variants (matches enum declaration order).
fn discriminant_cmp(a: &ZIRDiscriminant, b: &ZIRDiscriminant) -> Ordering {
    let order = |d: &ZIRDiscriminant| -> usize {
        match d {
            ZIRDiscriminant::Var => 0,
            ZIRDiscriminant::Constant => 1,
            ZIRDiscriminant::Add => 2,
            ZIRDiscriminant::Sub => 3,
            ZIRDiscriminant::Mul => 4,
            ZIRDiscriminant::Div => 5,
            ZIRDiscriminant::Rem => 6,
            ZIRDiscriminant::Pow => 7,
            ZIRDiscriminant::Dot => 8,
            ZIRDiscriminant::Concat => 9,
            ZIRDiscriminant::Neg => 10,
            ZIRDiscriminant::Pair => 11,
            ZIRDiscriminant::Random => 12,
            ZIRDiscriminant::Challenge => 13,
            ZIRDiscriminant::Log => 14,
            ZIRDiscriminant::Poly => 15,
            ZIRDiscriminant::Coef => 16,
            ZIRDiscriminant::Mle => 17,
            ZIRDiscriminant::Fft => 18,
            ZIRDiscriminant::Ifft => 19,
            ZIRDiscriminant::Interpolate => 20,
            ZIRDiscriminant::Evaluate => 21,
            ZIRDiscriminant::EvaluateGrid => 22,
            ZIRDiscriminant::EvaluateSelected => 23,
            ZIRDiscriminant::Ram => 24,
            ZIRDiscriminant::Vec => 25,
            ZIRDiscriminant::Record => 26,
            ZIRDiscriminant::Proj => 27,
            ZIRDiscriminant::Map => 28,
            ZIRDiscriminant::Reduce => 29,
            ZIRDiscriminant::Seq => 30,
            ZIRDiscriminant::Assert => 31,
            ZIRDiscriminant::Verify => 32,
        }
    };
    order(a).cmp(&order(b))
}

impl<C: ArkConfig + std::fmt::Debug> fmt::Display for ZIR<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ZIR::Var(s) => write!(f, "{s}"),
            ZIR::Constant(v) => write!(f, "{v:?}"),
            ZIR::Add(_) => write!(f, "+"),
            ZIR::Sub(_) => write!(f, "-"),
            ZIR::Mul(_) => write!(f, "*"),
            ZIR::Div(_) => write!(f, "/"),
            ZIR::Rem(_) => write!(f, "%"),
            ZIR::Pow(_) => write!(f, "^"),
            ZIR::Dot(_) => write!(f, "."),
            ZIR::Concat(_) => write!(f, "++"),
            ZIR::Neg(_) => write!(f, "neg"),
            ZIR::Pair(_) => write!(f, "pair"),
            ZIR::Random(s, _) => write!(f, "random[{s}]"),
            ZIR::Challenge(s, _) => write!(f, "challenge[{s}]"),
            ZIR::Log(s, _) => write!(f, "log[{s}]"),
            ZIR::Poly(_) => write!(f, "poly"),
            ZIR::Coef(_) => write!(f, "coef"),
            ZIR::Mle(_) => write!(f, "mle"),
            ZIR::Fft(_) => write!(f, "fft"),
            ZIR::Ifft(_) => write!(f, "ifft"),
            ZIR::Interpolate(_) => write!(f, "interpolate"),
            ZIR::Evaluate(_) => write!(f, "evaluate"),
            ZIR::EvaluateGrid(_) => write!(f, "evaluate_grid"),
            ZIR::EvaluateSelected(_) => write!(f, "evaluate_selected"),
            ZIR::Ram(_) => write!(f, "ram"),
            ZIR::Vec(_) => write!(f, "vec"),
            ZIR::Record(_, _) => write!(f, "record"),
            ZIR::Proj(s, _) => write!(f, ".{s}"),
            ZIR::Map(s, _) => write!(f, "map[{s}]"),
            ZIR::Reduce(op, _) => write!(f, "reduce[{op}]"),
            ZIR::Seq(_) => write!(f, "seq"),
            ZIR::Assert(_) => write!(f, "assert"),
            ZIR::Verify(_) => write!(f, "verify"),
        }
    }
}

// =====================================================================
// RIR — the runtime IR (ZIR + runtime-only ops)
// =====================================================================

/// The RIR e-graph language. See `docs/egraph-design-log.md` §3.3.
///
/// NOTE: RIR, RAnalysis, and RIRCost are temporarily in the egraph crate.
/// Once egraph is fully integrated, they should move to the runtime crate.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum RIR<C: ArkConfig> {
    // ---- all ZIR variants (copied) ----
    Var(Symbol),
    Constant(Value<C>),
    Add([Id; 2]),
    Sub([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),
    Rem([Id; 2]),
    Pow([Id; 2]),
    Dot([Id; 2]),
    Concat([Id; 2]),
    Neg([Id; 1]),
    Pair([Id; 2]),
    Random(Symbol, bool),
    Challenge(Symbol, bool),
    Log(Symbol, [Id; 1]),
    Poly([Id; 1]),
    Coef([Id; 1]),
    Mle([Id; 1]),
    Fft([Id; 1]),
    Ifft([Id; 1]),
    Interpolate([Id; 2]),
    Evaluate([Id; 2]),
    EvaluateGrid([Id; 1]),
    EvaluateSelected([Id; 3]),
    Ram([Id; 2]),
    Vec(Box<[Id]>),
    Record(Box<[Symbol]>, Box<[Id]>),
    Proj(Symbol, [Id; 1]),
    Map(Symbol, [Id; 2]),
    Reduce(BinOp, [Id; 1]),
    Seq([Id; 2]),
    Assert([Id; 2]),
    Verify([Id; 2]),
    // ---- runtime-only (NOT in ZIR) ----
    PowerGen([Id; 1]),
    SumcheckRound(Box<[Id]>),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum RIRDiscriminant {
    Var,
    Constant,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Dot,
    Concat,
    Neg,
    Pair,
    Random,
    Challenge,
    Log,
    Poly,
    Coef,
    Mle,
    Fft,
    Ifft,
    Interpolate,
    Evaluate,
    EvaluateGrid,
    EvaluateSelected,
    Ram,
    Vec,
    Record,
    Proj,
    Map,
    Reduce,
    Seq,
    Assert,
    Verify,
    PowerGen,
    SumcheckRound,
}

impl<C: ArkConfig + std::fmt::Debug> Language for RIR<C> {
    type Discriminant = RIRDiscriminant;

    fn discriminant(&self) -> Self::Discriminant {
        match self {
            RIR::Var(_) => RIRDiscriminant::Var,
            RIR::Constant(_) => RIRDiscriminant::Constant,
            RIR::Add(_) => RIRDiscriminant::Add,
            RIR::Sub(_) => RIRDiscriminant::Sub,
            RIR::Mul(_) => RIRDiscriminant::Mul,
            RIR::Div(_) => RIRDiscriminant::Div,
            RIR::Rem(_) => RIRDiscriminant::Rem,
            RIR::Pow(_) => RIRDiscriminant::Pow,
            RIR::Dot(_) => RIRDiscriminant::Dot,
            RIR::Concat(_) => RIRDiscriminant::Concat,
            RIR::Neg(_) => RIRDiscriminant::Neg,
            RIR::Pair(_) => RIRDiscriminant::Pair,
            RIR::Random(_, _) => RIRDiscriminant::Random,
            RIR::Challenge(_, _) => RIRDiscriminant::Challenge,
            RIR::Log(_, _) => RIRDiscriminant::Log,
            RIR::Poly(_) => RIRDiscriminant::Poly,
            RIR::Coef(_) => RIRDiscriminant::Coef,
            RIR::Mle(_) => RIRDiscriminant::Mle,
            RIR::Fft(_) => RIRDiscriminant::Fft,
            RIR::Ifft(_) => RIRDiscriminant::Ifft,
            RIR::Interpolate(_) => RIRDiscriminant::Interpolate,
            RIR::Evaluate(_) => RIRDiscriminant::Evaluate,
            RIR::EvaluateGrid(_) => RIRDiscriminant::EvaluateGrid,
            RIR::EvaluateSelected(_) => RIRDiscriminant::EvaluateSelected,
            RIR::Ram(_) => RIRDiscriminant::Ram,
            RIR::Vec(_) => RIRDiscriminant::Vec,
            RIR::Record(_, _) => RIRDiscriminant::Record,
            RIR::Proj(_, _) => RIRDiscriminant::Proj,
            RIR::Map(_, _) => RIRDiscriminant::Map,
            RIR::Reduce(_, _) => RIRDiscriminant::Reduce,
            RIR::Seq(_) => RIRDiscriminant::Seq,
            RIR::Assert(_) => RIRDiscriminant::Assert,
            RIR::Verify(_) => RIRDiscriminant::Verify,
            RIR::PowerGen(_) => RIRDiscriminant::PowerGen,
            RIR::SumcheckRound(_) => RIRDiscriminant::SumcheckRound,
        }
    }

    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (RIR::Var(a), RIR::Var(b)) => a == b,
            (RIR::Constant(a), RIR::Constant(b)) => a == b,
            (RIR::Add(_), RIR::Add(_))
            | (RIR::Sub(_), RIR::Sub(_))
            | (RIR::Mul(_), RIR::Mul(_))
            | (RIR::Div(_), RIR::Div(_))
            | (RIR::Rem(_), RIR::Rem(_))
            | (RIR::Pow(_), RIR::Pow(_))
            | (RIR::Dot(_), RIR::Dot(_))
            | (RIR::Concat(_), RIR::Concat(_))
            | (RIR::Neg(_), RIR::Neg(_))
            | (RIR::Pair(_), RIR::Pair(_))
            | (RIR::Poly(_), RIR::Poly(_))
            | (RIR::Coef(_), RIR::Coef(_))
            | (RIR::Mle(_), RIR::Mle(_))
            | (RIR::Fft(_), RIR::Fft(_))
            | (RIR::Ifft(_), RIR::Ifft(_))
            | (RIR::Interpolate(_), RIR::Interpolate(_))
            | (RIR::Evaluate(_), RIR::Evaluate(_))
            | (RIR::EvaluateGrid(_), RIR::EvaluateGrid(_))
            | (RIR::EvaluateSelected(_), RIR::EvaluateSelected(_))
            | (RIR::Ram(_), RIR::Ram(_))
            | (RIR::Seq(_), RIR::Seq(_))
            | (RIR::Assert(_), RIR::Assert(_))
            | (RIR::Verify(_), RIR::Verify(_))
            | (RIR::PowerGen(_), RIR::PowerGen(_)) => true,
            (RIR::Random(a, na), RIR::Random(b, nb)) => a == b && na == nb,
            (RIR::Challenge(a, na), RIR::Challenge(b, nb)) => a == b && na == nb,
            (RIR::Log(a, _), RIR::Log(b, _)) => a == b,
            (RIR::Record(an, _), RIR::Record(bn, _)) => an == bn,
            (RIR::Proj(a, _), RIR::Proj(b, _)) => a == b,
            (RIR::Map(a, _), RIR::Map(b, _)) => a == b,
            (RIR::Reduce(a, _), RIR::Reduce(b, _)) => a == b,
            (RIR::Vec(a), RIR::Vec(b)) => a.len() == b.len(),
            (RIR::SumcheckRound(a), RIR::SumcheckRound(b)) => a.len() == b.len(),
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            RIR::Var(_) | RIR::Constant(_) | RIR::Random(_, _) | RIR::Challenge(_, _) => &[],
            RIR::Add(ids)
            | RIR::Sub(ids)
            | RIR::Mul(ids)
            | RIR::Div(ids)
            | RIR::Rem(ids)
            | RIR::Pow(ids)
            | RIR::Dot(ids)
            | RIR::Concat(ids)
            | RIR::Pair(ids)
            | RIR::Interpolate(ids)
            | RIR::Evaluate(ids)
            | RIR::Ram(ids)
            | RIR::Seq(ids)
            | RIR::Assert(ids)
            | RIR::Verify(ids) => ids.as_slice(),
            RIR::Neg(ids)
            | RIR::Poly(ids)
            | RIR::Coef(ids)
            | RIR::Mle(ids)
            | RIR::Fft(ids)
            | RIR::Ifft(ids)
            | RIR::EvaluateGrid(ids)
            | RIR::Log(_, ids)
            | RIR::Proj(_, ids)
            | RIR::Reduce(_, ids)
            | RIR::PowerGen(ids) => ids.as_slice(),
            RIR::EvaluateSelected(ids) => ids.as_slice(),
            RIR::Map(_, ids) => ids.as_slice(),
            RIR::Vec(ids) => ids,
            RIR::Record(_, ids) => ids,
            RIR::SumcheckRound(ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            RIR::Var(_) | RIR::Constant(_) | RIR::Random(_, _) | RIR::Challenge(_, _) => &mut [],
            RIR::Add(ids)
            | RIR::Sub(ids)
            | RIR::Mul(ids)
            | RIR::Div(ids)
            | RIR::Rem(ids)
            | RIR::Pow(ids)
            | RIR::Dot(ids)
            | RIR::Concat(ids)
            | RIR::Pair(ids)
            | RIR::Interpolate(ids)
            | RIR::Evaluate(ids)
            | RIR::Ram(ids)
            | RIR::Seq(ids)
            | RIR::Assert(ids)
            | RIR::Verify(ids) => ids.as_mut_slice(),
            RIR::Neg(ids)
            | RIR::Poly(ids)
            | RIR::Coef(ids)
            | RIR::Mle(ids)
            | RIR::Fft(ids)
            | RIR::Ifft(ids)
            | RIR::EvaluateGrid(ids)
            | RIR::Log(_, ids)
            | RIR::Proj(_, ids)
            | RIR::Reduce(_, ids)
            | RIR::PowerGen(ids) => ids.as_mut_slice(),
            RIR::EvaluateSelected(ids) => ids.as_mut_slice(),
            RIR::Map(_, ids) => ids.as_mut_slice(),
            RIR::Vec(ids) => ids,
            RIR::Record(_, ids) => ids,
            RIR::SumcheckRound(ids) => ids,
        }
    }
}

impl<C: ArkConfig + std::fmt::Debug> PartialOrd for RIR<C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<C: ArkConfig + std::fmt::Debug> Ord for RIR<C> {
    fn cmp(&self, other: &Self) -> Ordering {
        let d1 = self.discriminant();
        let d2 = other.discriminant();
        let d_cmp = rir_discriminant_cmp(&d1, &d2);
        if d_cmp != Ordering::Equal {
            return d_cmp;
        }
        match (self, other) {
            (RIR::Var(a), RIR::Var(b)) => a.cmp(b),
            (RIR::Constant(a), RIR::Constant(b)) => a.cmp(b),
            (RIR::Add(a), RIR::Add(b)) => a.cmp(b),
            (RIR::Sub(a), RIR::Sub(b)) => a.cmp(b),
            (RIR::Mul(a), RIR::Mul(b)) => a.cmp(b),
            (RIR::Div(a), RIR::Div(b)) => a.cmp(b),
            (RIR::Rem(a), RIR::Rem(b)) => a.cmp(b),
            (RIR::Pow(a), RIR::Pow(b)) => a.cmp(b),
            (RIR::Dot(a), RIR::Dot(b)) => a.cmp(b),
            (RIR::Concat(a), RIR::Concat(b)) => a.cmp(b),
            (RIR::Neg(a), RIR::Neg(b)) => a.cmp(b),
            (RIR::Pair(a), RIR::Pair(b)) => a.cmp(b),
            (RIR::Random(a, na), RIR::Random(b, nb)) => a.cmp(b).then(na.cmp(nb)),
            (RIR::Challenge(a, na), RIR::Challenge(b, nb)) => a.cmp(b).then(na.cmp(nb)),
            (RIR::Log(a, _), RIR::Log(b, _)) => a.cmp(b),
            (RIR::Poly(a), RIR::Poly(b)) => a.cmp(b),
            (RIR::Coef(a), RIR::Coef(b)) => a.cmp(b),
            (RIR::Mle(a), RIR::Mle(b)) => a.cmp(b),
            (RIR::Fft(a), RIR::Fft(b)) => a.cmp(b),
            (RIR::Ifft(a), RIR::Ifft(b)) => a.cmp(b),
            (RIR::Interpolate(a), RIR::Interpolate(b)) => a.cmp(b),
            (RIR::Evaluate(a), RIR::Evaluate(b)) => a.cmp(b),
            (RIR::EvaluateGrid(a), RIR::EvaluateGrid(b)) => a.cmp(b),
            (RIR::EvaluateSelected(a), RIR::EvaluateSelected(b)) => a.cmp(b),
            (RIR::Ram(a), RIR::Ram(b)) => a.cmp(b),
            (RIR::Vec(a), RIR::Vec(b)) => a.cmp(b),
            (RIR::Record(an, _), RIR::Record(bn, _)) => an.cmp(bn),
            (RIR::Proj(a, _), RIR::Proj(b, _)) => a.cmp(b),
            (RIR::Map(a, _), RIR::Map(b, _)) => a.cmp(b),
            (RIR::Reduce(a, _), RIR::Reduce(b, _)) => a.cmp(b),
            (RIR::Seq(a), RIR::Seq(b)) => a.cmp(b),
            (RIR::Assert(a), RIR::Assert(b)) => a.cmp(b),
            (RIR::Verify(a), RIR::Verify(b)) => a.cmp(b),
            (RIR::PowerGen(a), RIR::PowerGen(b)) => a.cmp(b),
            (RIR::SumcheckRound(a), RIR::SumcheckRound(b)) => a.cmp(b),
            _ => Ordering::Equal,
        }
    }
}

fn rir_discriminant_cmp(a: &RIRDiscriminant, b: &RIRDiscriminant) -> Ordering {
    let order = |d: &RIRDiscriminant| -> usize {
        match d {
            RIRDiscriminant::Var => 0,
            RIRDiscriminant::Constant => 1,
            RIRDiscriminant::Add => 2,
            RIRDiscriminant::Sub => 3,
            RIRDiscriminant::Mul => 4,
            RIRDiscriminant::Div => 5,
            RIRDiscriminant::Rem => 6,
            RIRDiscriminant::Pow => 7,
            RIRDiscriminant::Dot => 8,
            RIRDiscriminant::Concat => 9,
            RIRDiscriminant::Neg => 10,
            RIRDiscriminant::Pair => 11,
            RIRDiscriminant::Random => 12,
            RIRDiscriminant::Challenge => 13,
            RIRDiscriminant::Log => 14,
            RIRDiscriminant::Poly => 15,
            RIRDiscriminant::Coef => 16,
            RIRDiscriminant::Mle => 17,
            RIRDiscriminant::Fft => 18,
            RIRDiscriminant::Ifft => 19,
            RIRDiscriminant::Interpolate => 20,
            RIRDiscriminant::Evaluate => 21,
            RIRDiscriminant::EvaluateGrid => 22,
            RIRDiscriminant::EvaluateSelected => 23,
            RIRDiscriminant::Ram => 24,
            RIRDiscriminant::Vec => 25,
            RIRDiscriminant::Record => 26,
            RIRDiscriminant::Proj => 27,
            RIRDiscriminant::Map => 28,
            RIRDiscriminant::Reduce => 29,
            RIRDiscriminant::Seq => 30,
            RIRDiscriminant::Assert => 31,
            RIRDiscriminant::Verify => 32,
            RIRDiscriminant::PowerGen => 33,
            RIRDiscriminant::SumcheckRound => 34,
        }
    };
    order(a).cmp(&order(b))
}

impl<C: ArkConfig + std::fmt::Debug> fmt::Display for RIR<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RIR::Var(s) => write!(f, "{s}"),
            RIR::Constant(v) => write!(f, "{v:?}"),
            RIR::Add(_) => write!(f, "+"),
            RIR::Sub(_) => write!(f, "-"),
            RIR::Mul(_) => write!(f, "*"),
            RIR::Div(_) => write!(f, "/"),
            RIR::Rem(_) => write!(f, "%"),
            RIR::Pow(_) => write!(f, "^"),
            RIR::Dot(_) => write!(f, "."),
            RIR::Concat(_) => write!(f, "++"),
            RIR::Neg(_) => write!(f, "neg"),
            RIR::Pair(_) => write!(f, "pair"),
            RIR::Random(s, _) => write!(f, "random[{s}]"),
            RIR::Challenge(s, _) => write!(f, "challenge[{s}]"),
            RIR::Log(s, _) => write!(f, "log[{s}]"),
            RIR::Poly(_) => write!(f, "poly"),
            RIR::Coef(_) => write!(f, "coef"),
            RIR::Mle(_) => write!(f, "mle"),
            RIR::Fft(_) => write!(f, "fft"),
            RIR::Ifft(_) => write!(f, "ifft"),
            RIR::Interpolate(_) => write!(f, "interpolate"),
            RIR::Evaluate(_) => write!(f, "evaluate"),
            RIR::EvaluateGrid(_) => write!(f, "evaluate_grid"),
            RIR::EvaluateSelected(_) => write!(f, "evaluate_selected"),
            RIR::Ram(_) => write!(f, "ram"),
            RIR::Vec(_) => write!(f, "vec"),
            RIR::Record(_, _) => write!(f, "record"),
            RIR::Proj(s, _) => write!(f, ".{s}"),
            RIR::Map(s, _) => write!(f, "map[{s}]"),
            RIR::Reduce(op, _) => write!(f, "reduce[{op}]"),
            RIR::Seq(_) => write!(f, "seq"),
            RIR::Assert(_) => write!(f, "assert"),
            RIR::Verify(_) => write!(f, "verify"),
            RIR::PowerGen(_) => write!(f, "powergen"),
            RIR::SumcheckRound(_) => write!(f, "sumcheck_round"),
        }
    }
}

// =====================================================================
// Analysis — ZData, ZAnalysis, RAnalysis
// =====================================================================

/// Per-e-class analysis data. See `docs/egraph-design-log.md` §3.4.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ZData {
    /// Type of this e-class (mirrors `Op::typ()`).
    pub typ: ATyp,
    /// Free binder tags referenced in this e-class.
    /// Used by broadcast (§4.iii) and LICM (§3.5 rule 12).
    pub free_vars: HashSet<Symbol>,
    /// Whether this e-class contains any visible side-effect node
    /// (Challenge/Log/Assert/Verify — NOT Random).
    /// Used for seq-elimination (§3.5 rule 8).
    pub has_visible_side_effect: bool,
    /// Whether this e-class contains any side-effect node at all
    /// (Random/Challenge/Log/Assert/Verify). Stricter — includes Random.
    /// Used for LICM (§3.5 rule 12).
    pub has_side_effect: bool,
}

impl Default for ZData {
    fn default() -> Self {
        ZData {
            typ: ATyp::unit(),
            free_vars: HashSet::new(),
            has_visible_side_effect: false,
            has_side_effect: false,
        }
    }
}

/// Analysis for ZIR e-graphs. See `docs/egraph-design-log.md` §3.4.
pub struct ZAnalysis<C: ArkConfig> {
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig> Default for ZAnalysis<C> {
    fn default() -> Self {
        ZAnalysis {
            _phantom: PhantomData,
        }
    }
}

impl<C: ArkConfig + std::fmt::Debug> Analysis<ZIR<C>> for ZAnalysis<C> {
    type Data = ZData;

    fn make(egraph: &mut EGraph<ZIR<C>, Self>, enode: &ZIR<C>, _id: Id) -> Self::Data {
        // Compute free_vars: union of children's, minus binder tag for Map
        let mut free_vars: HashSet<Symbol> = HashSet::new();
        enode.for_each(|id| {
            free_vars.extend(&egraph[id].data.free_vars);
        });

        // Side-effect flags from children
        let mut has_visible_side_effect = matches!(
            enode,
            ZIR::Challenge(_, _) | ZIR::Log(_, _) | ZIR::Assert(_) | ZIR::Verify(_)
        );
        let mut has_side_effect = matches!(
            enode,
            ZIR::Random(_, _)
                | ZIR::Challenge(_, _)
                | ZIR::Log(_, _)
                | ZIR::Assert(_)
                | ZIR::Verify(_)
        );
        enode.for_each(|id| {
            let d = &egraph[id].data;
            has_visible_side_effect |= d.has_visible_side_effect;
            has_side_effect |= d.has_side_effect;
        });

        // Map: subtract binder tag from body's free_vars
        // Map(tag, [dom, body]): free_vars = dom.fv ∪ (body.fv - {tag})
        match enode {
            ZIR::Map(tag, [dom_id, body_id]) => {
                let dom_fv = &egraph[*dom_id].data.free_vars;
                let body_fv = &egraph[*body_id].data.free_vars;
                free_vars = dom_fv.clone();
                free_vars.extend(body_fv.iter().filter(|s| *s != tag).cloned());
            }
            ZIR::Var(tag) => {
                free_vars.insert(*tag);
            }
            _ => {}
        }

        // Type inference: compute ATyp from children's types.
        // Falls back to ATyp::unit() when types are unknown or incompatible.
        let typ =
            {
                let child_typ = |id: Id| egraph[id].data.typ.clone();
                match enode {
                    ZIR::Constant(v) => v.typ(),
                    ZIR::Var(_) => ATyp::unit(), // binder var — type set by context
                    ZIR::Add([a, b]) => ATyp::lub_add(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Sub([a, b]) => ATyp::lub_sub(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Mul([a, b]) => ATyp::lub_mul(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Div([a, b]) => ATyp::lub_div(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Rem([a, b]) => ATyp::lub_rem(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Pow([a, b]) => ATyp::lub_pow(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Dot([a, b]) => ATyp::lub_dot(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Pair([a, b]) => ATyp::lub_pair(&child_typ(*a), &child_typ(*b), &Nothing)
                        .unwrap_or(ATyp::unit()),
                    ZIR::Neg([a]) => child_typ(*a),
                    ZIR::Poly([a]) => {
                        // Vec<F, k> → Uni(k-1)
                        match child_typ(*a) {
                            ATyp::Vec(_, n) if n > 0 => ATyp::uni(n - 1),
                            t => t,
                        }
                    }
                    ZIR::Coef([a]) => {
                        // Uni(m) → Vec<F, m+1>
                        match child_typ(*a) {
                            ATyp::Uni(m) => ATyp::vec_scalar(m + 1),
                            t => t,
                        }
                    }
                    ZIR::Fft([a]) => {
                        // Uni(m) → Vec<F, m+1>
                        match child_typ(*a) {
                            ATyp::Uni(m) => ATyp::vec_scalar(m + 1),
                            t => t,
                        }
                    }
                    ZIR::Ifft([a]) => {
                        // Vec<F, k> → Uni(k-1)
                        match child_typ(*a) {
                            ATyp::Vec(_, n) if n > 0 => ATyp::uni(n - 1),
                            t => t,
                        }
                    }
                    ZIR::Mle([a]) => child_typ(*a),
                    ZIR::Concat([a, b]) => {
                        ATyp::lub_concat(&child_typ(*a), &child_typ(*b), &Nothing)
                            .unwrap_or(ATyp::unit())
                    }
                    ZIR::Assert([_, _]) | ZIR::Verify([_, _]) => ATyp::unit(),
                    ZIR::Log(_, [_]) => ATyp::unit(),
                    ZIR::Seq([_, b]) => child_typ(*b),
                    ZIR::Random(_, _) | ZIR::Challenge(_, _) => ATyp::unit(),
                    // For Vec, Record, Map, Reduce, Ram, Interpolate, Evaluate,
                    // EvaluateGrid, EvaluateSelected, Proj — type inference is
                    // more complex; fall back to unit for now.
                    _ => ATyp::unit(),
                }
            };

        ZData {
            typ,
            free_vars,
            has_visible_side_effect,
            has_side_effect,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        // free_vars: set union
        let fv_changed = !b.free_vars.is_subset(&a.free_vars);
        a.free_vars.extend(b.free_vars);

        // Side-effect flags: OR
        let vse_changed = b.has_visible_side_effect && !a.has_visible_side_effect;
        a.has_visible_side_effect |= b.has_visible_side_effect;

        let se_changed = b.has_side_effect && !a.has_side_effect;
        a.has_side_effect |= b.has_side_effect;

        // typ: lub (equivalence) — if both are non-unit, take the lub;
        // if one is unit (unknown), keep the other.
        let typ_changed = if a.typ == ATyp::unit() && b.typ != ATyp::unit() {
            a.typ = b.typ.clone();
            true
        } else if a.typ != ATyp::unit() && b.typ == ATyp::unit() {
            false
        } else if a.typ != b.typ {
            a.typ = ATyp::lub_equ(&a.typ, &b.typ, &Nothing).unwrap_or(a.typ.clone());
            a.typ != b.typ
        } else {
            false
        };

        DidMerge(
            false,
            fv_changed || vse_changed || se_changed || typ_changed,
        )
    }

    // modify: NOT overridden — constant folding is done via rewrites (§4.vii)
}

/// Analysis for RIR e-graphs. Same logic as ZAnalysis, typed for RIR.
pub struct RAnalysis<C: ArkConfig> {
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig> Default for RAnalysis<C> {
    fn default() -> Self {
        RAnalysis {
            _phantom: PhantomData,
        }
    }
}

impl<C: ArkConfig + std::fmt::Debug> Analysis<RIR<C>> for RAnalysis<C> {
    type Data = ZData;

    fn make(egraph: &mut EGraph<RIR<C>, Self>, enode: &RIR<C>, _id: Id) -> Self::Data {
        let mut free_vars: HashSet<Symbol> = HashSet::new();
        enode.for_each(|id| {
            free_vars.extend(&egraph[id].data.free_vars);
        });

        let mut has_visible_side_effect = matches!(
            enode,
            RIR::Challenge(_, _) | RIR::Log(_, _) | RIR::Assert(_) | RIR::Verify(_)
        );
        let mut has_side_effect = matches!(
            enode,
            RIR::Random(_, _)
                | RIR::Challenge(_, _)
                | RIR::Log(_, _)
                | RIR::Assert(_)
                | RIR::Verify(_)
        );
        enode.for_each(|id| {
            let d = &egraph[id].data;
            has_visible_side_effect |= d.has_visible_side_effect;
            has_side_effect |= d.has_side_effect;
        });

        match enode {
            RIR::Map(tag, [dom_id, body_id]) => {
                let dom_fv = &egraph[*dom_id].data.free_vars;
                let body_fv = &egraph[*body_id].data.free_vars;
                free_vars = dom_fv.clone();
                free_vars.extend(body_fv.iter().filter(|s| *s != tag).cloned());
            }
            RIR::Var(tag) => {
                free_vars.insert(*tag);
            }
            _ => {}
        }

        ZData {
            typ: ATyp::unit(),
            free_vars,
            has_visible_side_effect,
            has_side_effect,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let fv_changed = !b.free_vars.is_subset(&a.free_vars);
        a.free_vars.extend(b.free_vars);
        let vse_changed = b.has_visible_side_effect && !a.has_visible_side_effect;
        a.has_visible_side_effect |= b.has_visible_side_effect;
        let se_changed = b.has_side_effect && !a.has_side_effect;
        a.has_side_effect |= b.has_side_effect;
        DidMerge(false, fv_changed || vse_changed || se_changed)
    }
}

// =====================================================================
// Cost functions — ZIRCost, RIRCost
// =====================================================================

/// Cost function for ZIR extraction.
/// Implements `CostFunction` (tree extraction via `Extractor`).
/// `LpCostFunction` (DAG extraction via `LpExtractor`) is available
/// behind the `lp` feature.
#[derive(Default)]
pub struct ZIRCost;

/// Per-node cost for ZIR (shared by both CostFunction and LpCostFunction).
fn zir_node_cost_u64<C: ArkConfig>(enode: &ZIR<C>) -> u64 {
    match enode {
        ZIR::Pair(_) => 1000,
        ZIR::Dot(_) => 15,
        ZIR::Fft(_) | ZIR::Ifft(_) | ZIR::Interpolate(_) => 500,
        ZIR::Evaluate(_) | ZIR::EvaluateGrid(_) | ZIR::EvaluateSelected(_) => 200,
        ZIR::Poly(_) | ZIR::Mle(_) | ZIR::Coef(_) => 100,
        ZIR::Map(..) | ZIR::Reduce(..) => 80,
        ZIR::Neg(_) => 5,
        ZIR::Add(_) | ZIR::Sub(_) | ZIR::Mul(_) | ZIR::Div(_) => 10,
        ZIR::Assert(_) | ZIR::Verify(_) | ZIR::Seq(_) => 1,
        ZIR::Constant(_) | ZIR::Var(_) => 1,
        _ => 50,
    }
}

impl<C: ArkConfig + std::fmt::Debug> CostFunction<ZIR<C>> for ZIRCost {
    type Cost = u64;
    fn cost<Costs>(&mut self, enode: &ZIR<C>, mut costs: Costs) -> Self::Cost
    where
        Costs: FnMut(Id) -> Self::Cost,
    {
        let op_cost = zir_node_cost_u64(enode);
        op_cost + enode.fold(0, |sum, id| sum + costs(id))
    }
}

/// Cost function for RIR extraction.
/// Same weights as ZIRCost for shared ops, plus runtime-only entries.
#[derive(Default)]
pub struct RIRCost;

fn rir_node_cost_u64<C: ArkConfig>(enode: &RIR<C>) -> u64 {
    match enode {
        RIR::Pair(_) => 1000,
        RIR::Dot(_) => 15,
        RIR::Fft(_) | RIR::Ifft(_) | RIR::Interpolate(_) => 500,
        RIR::Evaluate(_) | RIR::EvaluateGrid(_) | RIR::EvaluateSelected(_) => 200,
        RIR::Poly(_) | RIR::Mle(_) | RIR::Coef(_) => 100,
        RIR::Map(..) | RIR::Reduce(..) => 80,
        RIR::Neg(_) => 5,
        RIR::Add(_) | RIR::Sub(_) | RIR::Mul(_) | RIR::Div(_) => 10,
        RIR::Assert(_) | RIR::Verify(_) | RIR::Seq(_) => 1,
        RIR::Constant(_) | RIR::Var(_) => 1,
        RIR::PowerGen(_) => 50,
        RIR::SumcheckRound(_) => 200,
        _ => 50,
    }
}

impl<C: ArkConfig + std::fmt::Debug> CostFunction<RIR<C>> for RIRCost {
    type Cost = u64;
    fn cost<Costs>(&mut self, enode: &RIR<C>, mut costs: Costs) -> Self::Cost
    where
        Costs: FnMut(Id) -> Self::Cost,
    {
        let op_cost = rir_node_cost_u64(enode);
        op_cost + enode.fold(0, |sum, id| sum + costs(id))
    }
}

// =====================================================================
// Record construction helper
// =====================================================================

/// Create a Record e-node with field names sorted by Symbol.
/// This is the only way Record should be constructed (in conv.rs,
/// in rewrites) to ensure deterministic hashing.
pub fn make_record<C: ArkConfig + std::fmt::Debug>(
    egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
    fields: Vec<(Symbol, Id)>,
) -> Id {
    let mut fields = fields;
    fields.sort_by_key(|a| a.0);
    let names: Box<[Symbol]> = fields.iter().map(|(s, _)| *s).collect();
    let values: Box<[Id]> = fields.iter().map(|(_, id)| *id).collect();
    egraph.add(ZIR::Record(names, values))
}

/// Create an RIR Record e-node with field names sorted by Symbol.
pub fn make_rir_record<C: ArkConfig + std::fmt::Debug>(
    egraph: &mut EGraph<RIR<C>, RAnalysis<C>>,
    fields: Vec<(Symbol, Id)>,
) -> Id {
    let mut fields = fields;
    fields.sort_by_key(|a| a.0);
    let names: Box<[Symbol]> = fields.iter().map(|(s, _)| *s).collect();
    let values: Box<[Id]> = fields.iter().map(|(_, id)| *id).collect();
    egraph.add(RIR::Record(names, values))
}
