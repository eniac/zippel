// mod model;
// pub use model::AsymptoticCostModel;
use crate::arkworks::{ATyp, ArkConfig};
use crate::graph::Op;

pub trait CostModel<C: ArkConfig> {
    fn cost(&mut self, op: &Op<C>, nthreads: usize) -> f64;
}
