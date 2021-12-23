use std::{
  vec::Vec,
  boxed::Box,
};
use tailcall::trampoline;
use im::Vector;
use crate::block::*;

#[derive(Debug, Clone)]
pub enum Value {
  Papp(Neutral, Args),
  VLam(TermPtr, Env),
}

#[derive(Debug, Clone)]
pub enum Neutral {
  FVar(u32),
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
  (heap.len()-1) as ValuePtr
}

#[inline(always)]
pub fn vlam(term: TermPtr, env: Env, heap: &mut Heap) -> ValuePtr {
  heap.push(Value::VLam(term, env));
  (heap.len()-1) as ValuePtr
}

pub type Heap = Vec<Value>;
pub type ValuePtr = u32;

pub type Continuation = Option<Box<Node>>;

pub struct Node {
  term: TermPtr,
  env: Env,
  args: Args,
  cont: Continuation,
}

#[inline(always)]
fn cont_or_ret<'a>(
  store: &'a Store, heap: &'a mut Heap, val: ValuePtr, cont: Continuation
) -> trampoline::Next<(&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation), ValuePtr> {
  match cont {
    None => trampoline::Finish(val),
    Some(mut ctx) => {
      ctx.env.push_front(val);
      trampoline::Recurse((store, heap, ctx.term, ctx.env, ctx.args, ctx.cont))
    },
  }
}

#[inline(always)]
pub fn eval_step<'a>(
  (store, heap, term, env, mut args, mut cont): (&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation)
) -> trampoline::Next<(&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation), ValuePtr> {
  match store[term as usize] {
    Block::App(fun, arg) => {
      args.push((arg, env.clone()));
      trampoline::Recurse((store, heap, fun, env, args, cont))
    },
    Block::Lam(bod) => {
      match args.pop() {
        Some((exp, exp_env)) => {
          cont = Some(
            Box::new(Node {
              term: bod,
              env: env,
              args,
              cont,
            })
          );
          trampoline::Recurse((store, heap, exp, exp_env, vec![], cont))
        },
        None => {
          let val = vlam(bod, env, heap);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Var(idx) => {
      let val = env[idx as usize];
      if args.is_empty() {
	cont_or_ret(store, heap, val, cont)
      }
      else {
        match &heap[val as usize] {
          Value::Papp(neu, p_args) => {
            args.extend_from_slice(p_args);
            let val = papp(neu.clone(), args, heap);
	    cont_or_ret(store, heap, val, cont)
          }
          Value::VLam(bod, env) => {
            let (exp, exp_env) = args.pop().unwrap();
            cont = Some(
              Box::new(Node {
                term: *bod,
                env: env.clone(),
                args,
                cont,
              })
            );
            trampoline::Recurse((store, heap, exp, exp_env, vec![], cont))
          },
        }
      }
    },
    Block::Int(int) => {
      let val = papp(Neutral::Int(int), args, heap);
      cont_or_ret(store, heap, val, cont)
    },
    Block::Ref(idx) => {
      trampoline::Recurse((store, heap, idx, env, args, cont))
    },
    Block::Add(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a+b), args, heap);
	    cont_or_ret(store, heap, val, cont)
          }
        _ => {
          let val = papp(Neutral::Add(Box::new((val1, val2))), args, heap);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Sub(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a-b), args, heap);
	    cont_or_ret(store, heap, val, cont)
          }
        _ => {
          let val = papp(Neutral::Sub(Box::new((val1, val2))), args, heap);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Mul(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a*b), args, heap);
	    cont_or_ret(store, heap, val, cont)
          }
        _ => {
          let val = papp(Neutral::Mul(Box::new((val1, val2))), args, heap);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Eqz(idx, case1, case2) => {
      let val = env[idx as usize];
      match &heap[val as usize] {
        Value::Papp(Neutral::Int(a), args_a)
          if args_a.is_empty() => {
            if *a == 0 {
              trampoline::Recurse((store, heap, case1, env, args, cont))
            }
            else {
              trampoline::Recurse((store, heap, case2, env, args, cont))
            }
          }
        _ => {
          let val = papp(Neutral::Eqz(Box::new((idx, env, case1, case2))), args, heap);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Impossible => unreachable!(),
  }
}

pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, env: Env, args: Args) -> ValuePtr {
  trampoline::run(eval_step, (store, heap, term, env, args, None))
}
