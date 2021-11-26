use std::{
  vec::Vec,
  boxed::Box,
};
use im::Vector;
use crate::term::*;

pub type Env = Vector<ValuePtr>;
pub type Args = Vec<ValuePtr>;

#[derive(Debug, Clone)]
pub enum Value {
  Papp(Neutral, Args),
  VLam(TermPtr, Box<Env>),
}

#[inline(always)]
pub fn papp(neu: Neutral, args: Args, heap: &mut Heap) -> ValuePtr {
  heap.push(Value::Papp(neu, args));
  (heap.len()-1) as ValuePtr
}

#[inline(always)]
pub fn vlam(term: TermPtr, env: Env, heap: &mut Heap) -> ValuePtr {
  heap.push(Value::VLam(term, Box::new(env)));
  (heap.len()-1) as ValuePtr
}

#[derive(Debug, Clone)]
pub enum Neutral {
  FVar(EnvPtr),
  Int(i64),
  Add(Box<(ValuePtr, ValuePtr)>),
  Mul(Box<(ValuePtr, ValuePtr)>),
  Sub(Box<(ValuePtr, ValuePtr)>),
  Eqz(Box<(ValuePtr, Env, TermPtr, TermPtr)>),
}

pub type Heap = Vec<Value>;
pub type ValuePtr = u32;

pub enum State {
  Ret(TermPtr, Env),
  Arg(ValuePtr),
}

#[inline]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr) -> ValuePtr {
  macro_rules! apply {
    ($heap:ident, $stack:ident, $node:ident, $env:ident, $neu:expr, $args:ident) => {
      loop {
        match $stack.pop() {
          Some(State::Arg(arg)) => {
            $args.push(arg);
          },
          Some(State::Ret(exp, exp_env)) => {
            $node = exp;
            $env = exp_env.clone();
            $stack.push(State::Arg(papp($neu, $args, $heap)));
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
    match store[node as usize] {
      Term::App(fun, arg) => {
        stack.push(State::Ret(fun, env.clone()));
        node = arg;
      },
      Term::Lam(bod) => {
        match stack.pop() {
          Some(State::Arg(arg)) => {
            node = bod;
            env.push_back(arg);
          },
          Some(State::Ret(exp, exp_env)) => {
            let value = vlam(bod, env.clone(), heap);
            node = exp;
            env = exp_env.clone();
            stack.push(State::Arg(value))
          },
          None => {
            return vlam(bod, env, heap);
          },
        }
      },
      Term::Var(idx) => {
        let value = env[env.len() - 1 - idx as usize];
        match stack.pop() {
          Some(State::Arg(arg)) => {
            match &heap[value as usize] {
              Value::Papp(neu, p_args) => {
                let mut args = p_args.clone();
                args.push(arg);
                apply!(heap, stack, node, env, neu.clone(), args);
              },
              Value::VLam(bod, lam_env) => {
                node = *bod;
                env = (&**lam_env).clone();
                env.push_back(arg);
              }
            }
          },
          Some(State::Ret(exp, exp_env)) => {
            node = exp;
            env = exp_env.clone();
            stack.push(State::Arg(value))
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
        let val1 = env[env.len() - 1 - idx1 as usize];
        let val2 = env[env.len() - 1 - idx2 as usize];
        let neu = match (&heap[val1 as usize], &heap[val2 as usize]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1+num2),
          _ => Neutral::Add(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Mul(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1 as usize];
        let val2 = env[env.len() - 1 - idx2 as usize];
        let neu = match (&heap[val1 as usize], &heap[val2 as usize]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1*num2),
          _ => Neutral::Mul(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Sub(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1 as usize];
        let val2 = env[env.len() - 1 - idx2 as usize];
        let neu = match (&heap[val1 as usize], &heap[val2 as usize]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1-num2),
          _ => Neutral::Sub(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Term::Eqz(idx, case1, case2) => {
        let val = env[env.len() - 1 - idx as usize];
        match &heap[val as usize] {
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
