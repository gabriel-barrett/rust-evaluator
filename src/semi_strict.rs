use std::{
  vec::Vec,
  boxed::Box,
};
use im::Vector;
use crate::term::*;

#[derive(Debug, Clone)]
pub enum Value {
  Papp(Neutral, Args),
  VLam(TermPtr, Env),
}

#[derive(Debug, Clone)]
pub enum Neutral {
  FVar(usize),
  Int(i64),
  Add(Box<(ValuePtr, ValuePtr)>),
  Mul(Box<(ValuePtr, ValuePtr)>),
  Sub(Box<(ValuePtr, ValuePtr)>),
  Eqz(Box<(ValuePtr, Env, TermPtr, TermPtr)>),
}

pub type Thunk = (TermPtr, Env);
pub type Env = Vector<ValuePtr>;
pub type Args = Vec<Thunk>;

#[inline(always)]
pub fn papp(neu: Neutral, args: Args, heap: &mut Heap) -> ValuePtr {
  heap.push(Value::Papp(neu, args));
  heap.len()-1
}

#[inline(always)]
pub fn vlam(term: TermPtr, env: Env, heap: &mut Heap) -> ValuePtr {
  heap.push(Value::VLam(term, env));
  heap.len()-1
}

pub type Heap = Vec<Value>;
pub type ValuePtr = usize;

pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, mut env: Env, mut args: Args) -> ValuePtr {
  match store[term] {
    Term::App(fun, arg) => {
      args.push((arg, env.clone()));
      eval(store, heap, fun, env, args)
    },
    Term::Lam(bod) => {
      match args.pop() {
        Some((exp, exp_env)) => {
          let arg = eval(store, heap, exp, exp_env, vec![]);
          env.push_front(arg);
          eval (store, heap, bod, env, args)
        },
        None => {
          vlam(bod, env, heap)
        },
      }
    },
    Term::Var(idx) => {
      let val = env[idx];
      apply(store, heap, val, args)
    },
    Term::Int(int) => {
      papp(Neutral::Int(int), args, heap)
    },
    Term::Ref(idx) => {
      eval(store, heap, idx, env, args)
    },
    Term::Add(idx1, idx2) => {
      let val1 = env[idx1];
      let val2 = env[idx2];
      match (&heap[val1], &heap[val2]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            papp(Neutral::Int(a+b), args, heap)
          }
        _ => {
          papp(Neutral::Add(Box::new((val1, val2))), args, heap)
        },
      }
    },
    Term::Sub(idx1, idx2) => {
      let val1 = env[idx1];
      let val2 = env[idx2];
      match (&heap[val1], &heap[val2]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            papp(Neutral::Int(a-b), args, heap)
          }
        _ => {
          papp(Neutral::Sub(Box::new((val1, val2))), args, heap)
        },
      }
    },
    Term::Mul(idx1, idx2) => {
      let val1 = env[idx1];
      let val2 = env[idx2];
      match (&heap[val1], &heap[val2]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            papp(Neutral::Int(a*b), args, heap)
          }
        _ => {
          papp(Neutral::Mul(Box::new((val1, val2))), args, heap)
        },
      }
    },
    Term::Eqz(idx, case1, case2) => {
      let val = env[idx];
      match &heap[val] {
        Value::Papp(Neutral::Int(a), args_a)
          if args_a.is_empty() => {
            if *a == 0 {
              eval(store, heap, case1, env, args)
            }
            else {
              eval(store, heap, case2, env, args)
            }
          }
        _ => {
          papp(Neutral::Eqz(Box::new((idx, env, case1, case2))), args, heap)
        },
      }
    },
    Term::Impossible => unreachable!(),
  }
}

pub fn apply(store: &Store, heap: &mut Heap, val: ValuePtr, mut args: Args) -> ValuePtr {
  if args.is_empty() {
    val
  }
  else {
    match &heap[val] {
      Value::Papp(neu, p_args) => {
        args.extend_from_slice(p_args);
        papp(neu.clone(), args, heap)
      }
      Value::VLam(bod, env) => {
        let term = *bod;
        let mut env = env.clone();
        let (exp, exp_env) = args.pop().unwrap();
        let arg = eval(store, heap, exp, exp_env, vec![]);
        env.push_front(arg);
        eval(store, heap, term, env, args)
      },
    }
  }
}
