use std::{
  mem::ManuallyDrop,
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

pub struct State {
  kind: Kind,
  inner: InnerState,
}

#[derive(Debug, Clone, Copy)]
pub enum Kind {
  Ret,
  Arg,
}

#[repr(C)]
pub union InnerState {
    ret: ManuallyDrop<(TermPtr, Env)>,
    arg: ValuePtr,
}


#[inline]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr) -> ValuePtr {
  macro_rules! apply {
    ($heap:ident, $stack:ident, $node:ident, $env:ident, $neu:expr, $args:ident) => {
      loop {
        match $stack.pop() {
          Some(State { kind: Kind::Arg, inner }) => {
            unsafe { $args.push(inner.arg); }
          },
          Some(State { kind: Kind::Ret, inner }) => {
            let (exp, exp_env) = unsafe { ManuallyDrop::into_inner(inner.ret) };
            $node = exp;
            $env = exp_env;
            let inner = InnerState{ arg: papp($neu, $args, $heap) };
            $stack.push(State { kind: Kind::Arg, inner });
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
        let inner = InnerState{ ret: ManuallyDrop::new((fun, env.clone())) };
        stack.push(State { kind: Kind::Ret, inner });
        node = arg;
      },
      Term::Lam(bod) => {
        match stack.last_mut() {
          Some(State { kind: Kind::Arg, inner }) => {
            node = bod;
            unsafe { env.push_back(inner.arg) };
            stack.pop();
          },
          Some(State { kind: kind @ Kind::Ret, inner }) => {
            let value = vlam(bod, env.clone(), heap);
            let (exp, exp_env) = unsafe { ManuallyDrop::take(&mut inner.ret) };
            inner.arg = value;
            *kind = Kind::Arg;
            node = exp;
            env = exp_env;
          },
          None => {
            return vlam(bod, env, heap);
          },
        }
      },
      Term::Var(idx) => {
        let value = env[env.len() - 1 - idx as usize];
        match stack.last_mut() {
          Some(State { kind: Kind::Arg, inner }) => {
            let arg = unsafe { inner.arg };
            match &heap[value as usize] {
              Value::Papp(neu, p_args) => {
                let mut args = p_args.clone();
                apply!(heap, stack, node, env, neu.clone(), args);
              },
              Value::VLam(bod, lam_env) => {
                node = *bod;
                env = (&**lam_env).clone();
                env.push_back(arg);
                stack.pop();
              }
            }
          },
          Some(State { kind: kind @ Kind::Ret, inner }) => {
            let (exp, exp_env) = unsafe { ManuallyDrop::take(&mut inner.ret) };
            inner.arg = value;
            *kind = Kind::Arg;
            node = exp;
            env = exp_env;
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
            let neu = Neutral::Eqz(Box::new((idx, env, case1, case2)));
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
