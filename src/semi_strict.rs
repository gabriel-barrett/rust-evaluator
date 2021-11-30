use std::{
  vec::Vec,
  boxed::Box,
};
use tailcall::tailcall;
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

#[tailcall]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, env: Env, mut args: Args, mut cont: Continuation) -> ValuePtr {
  match store[term as usize] {
    Block::App(fun, arg) => {
      args.push((arg, env.clone()));
      eval(store, heap, fun, env, args, cont)
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
          eval(store, heap, exp, exp_env, vec![], cont)
        },
        None => {
          let val = vlam(bod, env, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.env.push_front(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        },
      }
    },
    Block::Var(idx) => {
      let val = env[idx as usize];
      if args.is_empty() {
        match cont {
          None => val,
          Some(mut ctx) => {
            ctx.env.push_front(val);
            eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
          },
        }
      }
      else {
        match &heap[val as usize] {
          Value::Papp(neu, p_args) => {
            args.extend_from_slice(p_args);
            let val = papp(neu.clone(), args, heap);
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.env.push_front(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
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
            eval(store, heap, exp, exp_env, vec![], cont)
          },
        }
      }
    },
    Block::Int(int) => {
      let val = papp(Neutral::Int(int), args, heap);
      match cont {
        None => val,
        Some(mut ctx) => {
          ctx.env.push_front(val);
          eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
        },
      }
    },
    Block::Ref(idx) => {
      eval(store, heap, idx, env, args, cont)
    },
    Block::Add(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a+b), args, heap);
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.env.push_front(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        _ => {
          let val = papp(Neutral::Add(Box::new((val1, val2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.env.push_front(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
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
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.env.push_front(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        _ => {
          let val = papp(Neutral::Sub(Box::new((val1, val2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.env.push_front(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
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
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.env.push_front(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        _ => {
          let val = papp(Neutral::Mul(Box::new((val1, val2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.env.push_front(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        },
      }
    },
    Block::Eqz(idx, case1, case2) => {
      let val = env[idx as usize];
      match &heap[val as usize] {
        Value::Papp(Neutral::Int(a), args_a)
          if args_a.is_empty() => {
            if *a == 0 {
              eval(store, heap, case1, env, args, cont)
            }
            else {
              eval(store, heap, case2, env, args, cont)
            }
          }
        _ => {
          let val = papp(Neutral::Eqz(Box::new((idx, env, case1, case2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.env.push_front(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        },
      }
    },
    Block::Impossible => unreachable!(),
  }
}
