// mod model;
// pub use model::AsymptoticCostModel;
use backend::{ATyp, ArkConfig};
use graph::Op;

pub trait CostModel<C: ArkConfig> {
    fn cost(&mut self, op: &Op<C>, nthreads: usize) -> f64;
}
