use share::Ctx;

/// A trait for evaluating expressions
pub trait Eval {
    type Value;
    type Id;
    type Error;
    fn eval(&self, ctx: &Ctx<Self::Id, Self::Value>) -> Result<Self::Value, Self::Error>;
}

