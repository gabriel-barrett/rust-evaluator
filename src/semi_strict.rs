use std::{
  vec::Vec,
  boxed::Box,
};
use im::Vector;
use crate::term::*;

pub type Thunk = (TermPtr, Env);
pub type Env = Vector<ValuePtr>;
pub type Args = Vec<Thunk>;

#[derive(Debug, Clone)]
pub enum Value {
  Papp(Neutral, Args),
  VLam(TermPtr, Env),
}

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

#[derive(Debug, Clone)]
pub enum Neutral {
  FVar(usize),
  Int(i64),
  Add(Box<(ValuePtr, ValuePtr)>),
  Mul(Box<(ValuePtr, ValuePtr)>),
  Sub(Box<(ValuePtr, ValuePtr)>),
  Eqz(Box<(ValuePtr, Env, TermPtr, TermPtr)>),
}

pub type Heap = Vec<Value>;
pub type ValuePtr = usize;

pub enum State {
  Ext(TermPtr, Env),
  Arg(TermPtr, Env),
}

#[inline]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr) -> ValuePtr {
  macro_rules! apply {
    ($heap:ident, $stack:ident, $node:ident, $env:ident, $neu:expr, $args:ident) => {
      loop {
        match $stack.pop() {
          Some(State::Arg(exp, exp_env)) => {
            $args.push((exp, exp_env));
          },
          Some(State::Ext(exp, exp_env)) => {
            $node = exp;
            $env = exp_env.clone(); 
            $env.push_back(papp($neu, $args, $heap));
            break
          },
          None => return papp($neu, $args, $heap),
        }
      }
    }
  }

  let mut node = term;
  let mut env: Env = Vector::new();
  let mut stack = vec![];
  loop {
    match store[node] {
      Term::App(fun, arg) => {
        stack.push(State::Arg(arg, env.clone()));
        node = fun;
      },
      Term::Lam(bod) => {
        match stack.pop() {
          Some(State::Arg(exp, exp_env)) => {
            stack.push(State::Ext(bod, env.clone()));
            node = exp;
            env = exp_env.clone();
          },
          Some(State::Ext(exp, exp_env)) => {
            let value = vlam(bod, env.clone(), heap);
            node = exp;
            env = exp_env.clone();
            env.push_back(value);
          },
          None => {
            return vlam(bod, env, heap);
          },
        }
      },
      Term::Var(idx) => {
        let value = env[env.len() - 1 - idx];
        match stack.pop() {
          Some(State::Ext(exp, exp_env)) => {
            node = exp;
            env = exp_env.clone();
            env.push_back(value);
          },
          Some(State::Arg(exp, exp_env)) => {
            match &heap[value] {
              Value::VLam(bod, lam_env) => {
                stack.push(State::Ext(*bod, lam_env.clone()));
                node = exp;
                env = exp_env.clone();
              },
              Value::Papp(neu, p_args) => {
                let mut args = p_args.clone();
                args.push((exp, exp_env));
                apply!(heap, stack, node, env, neu.clone(), args);
              },
            }
          },
          None => {
            return value;
          },
        }
      },
      Term::Ref(idx) => {
        node = idx;
      },
      Term::Int(num) => {
        let neu = Neutral::Int(num);
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Add(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1];
        let val2 = env[env.len() - 1 - idx2];
        let neu = match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1+num2),
          _ => Neutral::Add(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Mul(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1];
        let val2 = env[env.len() - 1 - idx2];
        let neu = match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1*num2),
          _ => Neutral::Mul(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Sub(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1];
        let val2 = env[env.len() - 1 - idx2];
        let neu = match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1-num2),
          _ => Neutral::Sub(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Eqz(idx, case1, case2) => {
        let val = env[env.len() - 1 - idx];
        match &heap[val] {
          Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
            if *num == 0 {
              node = case1;
            }
            else {
              node = case2;
            }
          },
          _ => {
            let neu = Neutral::Eqz(Box::new((idx, env.clone(), case1, case2)));
            let mut args = vec![];
            apply!(heap, stack, node, env, neu, args);
          },
        }
      },
      Term::Impossible => {
        unreachable!()
      },
    }
  }
}
