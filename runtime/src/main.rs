#![feature(box_patterns)]
use std::thread;
use std::time::{Duration, SystemTime};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Type {
    Int,
    Bool
}
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Value {
    Int(i32),
    Bool(bool)
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Exp {
    Combine(Box<Exp>, Box<Exp>),
    Var(usize),
    Value(Value)
}

fn unify(ta: Type, tb: Type) -> Type {
    if ta == tb {
        ta
    } else {
        panic!("Type error {:?} != {:?}", ta, tb);
    }
}

fn infer(exp: Exp, ctx: &Vec<Type>) -> Type {
    match exp {
        Exp::Var(i) => ctx[i],
        Exp::Value(Value::Int(_)) => Type::Int,
        Exp::Value(Value::Bool(_)) => Type::Bool,
        Exp::Combine(box a, box b) => {
            let ta = infer(a, ctx);
            let tb = infer(b, ctx);
            unify(ta, tb)
        }
    }
}

type Closure = Box<dyn Fn(Vec<Value>) -> Value>;
fn stage(exp: Exp) -> Closure {
    // artificial delay
    std::thread::sleep(std::time::Duration::from_secs(2));
    match exp {
        Exp::Var(i) => Box::new(move |v: Vec<Value>| v[i]),
        Exp::Combine(box a, box b) => {
            let fa = stage(a);
            let fb = stage(b);
            Box::new(move |v| match (fa(v.clone()), fb(v)) {
                (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
                (Value::Bool(a), Value::Bool(b)) => Value::Bool(a && b),
                (_, _) => panic!("Type error")
            })
        },
        Exp::Value(v) => Box::new(move |_| v)
    }
}

impl Exp {
    pub fn combine(a: Exp, b: Exp) -> Exp {
        Exp::Combine(Box::new(a), Box::new(b))
    }
    pub fn bool(b: bool) -> Exp {
        Exp::Value(Value::Bool(b))
    }

    pub fn int(i: i32) -> Exp {
        Exp::Value(Value::Int(i))
    }
}

fn main() {
    let ex1 = Exp::combine(Exp::Var(0), Exp::bool(false));
    println!("[{:?}] Staging {:?}", SystemTime::now(), ex1);
    let f = stage(ex1.clone());
    let inputs = vec![Value::Bool(true)];
    println!("[{:?}] Evaluating {:?}", SystemTime::now(), ex1);
    println!("Result {:?}", f(inputs));
}
