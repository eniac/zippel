//! `/` and `%` for tests, which divide by nonzero values. Elsewhere a division
//! goes through [`Value::value_bin`], which reports a zero divisor.

use super::Value;
use crate::Backend;
use lang::ast::BinOp;
use std::ops::{Div, Rem};

impl<C: Backend> Div for Value<C> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        self.value_bin(BinOp::Div, other)
            .expect("a test divided by zero")
    }
}

impl<C: Backend> Rem for Value<C> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        self.value_bin(BinOp::Rem, other)
            .expect("a test divided by zero")
    }
}

impl<C: Backend> Div for &Value<C> {
    type Output = Value<C>;

    fn div(self, other: Self) -> Value<C> {
        self.clone() / other.clone()
    }
}

impl<C: Backend> Rem for &Value<C> {
    type Output = Value<C>;

    fn rem(self, other: Self) -> Value<C> {
        self.clone() % other.clone()
    }
}
