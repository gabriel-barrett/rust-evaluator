use std::{
  vec::Vec,
  boxed::Box,
};
use tailcall::tailcall;
use im::Vector;
use crate::block::*;

#[derive(Debug, Clone)]
pub enum Value {
  VNeu(Neutral),
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

pub type Env = Vector<ValuePtr>;
pub type Args = Vec<ValuePtr>;

#[inline(always)]
pub fn vneu(neu: Neutral, heap: &mut Heap) -> ValuePtr {
  heap.push(Value::VNeu(neu));
  (heap.len()-1) as ValuePtr
}

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

pub fn vneu_or_papp(neu: Neutral, args: Args, heap: &mut Heap) -> ValuePtr {
  if args.len() == 0 {
    vneu(neu, heap)
  }
  else {
    papp(neu, args, heap)
  }
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
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, mut env: Env, mut args: Args, mut cont: Continuation) -> ValuePtr {
  match store[term as usize] {
    Block::App(fun, arg) => {
      cont = Some(
        Box::new(Node {
          term: fun,
          env: env.clone(),
          args,
          cont,
        })
      );
      eval(store, heap, arg, env, vec![], cont)
    },
    Block::Lam(bod) => {
      match args.pop() {
        Some(arg) => {
          env.push_front(arg);
          eval (store, heap, bod, env, args, cont)
        },
        None => {
          let val = vlam(bod, env, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
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
            ctx.args.push(val);
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
                ctx.args.push(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
          Value::VLam(bod, env) => {
            let mut env = env.clone();
            env.push_front(args.pop().unwrap());
            let term = *bod;
            eval(store, heap, term, env, args, cont)
          },
          Value::VNeu(neu) => {
            let val = vneu_or_papp(neu.clone(), args, heap);
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.args.push(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        }
      }
    },
    Block::Int(int) => {
      let val = vneu_or_papp(Neutral::Int(int), args, heap);
      match cont {
        None => val,
        Some(mut ctx) => {
          ctx.args.push(val);
          eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
        },
      }
    },
    Block::Ref(idx) => {
      eval(store, heap, idx, Vector::new(), args, cont)
    },
    Block::Add(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Value::VNeu(Neutral::Int(a)), Value::VNeu(Neutral::Int(b))) => {
          let val = vneu_or_papp(Neutral::Int(a+b), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        }
        _ => {
          let val = vneu_or_papp(Neutral::Add(Box::new((val1, val2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
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
        (Value::VNeu(Neutral::Int(a)), Value::VNeu(Neutral::Int(b))) => {
          let val = vneu_or_papp(Neutral::Int(a-b), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        }
        _ => {
          let val = vneu_or_papp(Neutral::Sub(Box::new((val1, val2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
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
        (Value::VNeu(Neutral::Int(a)), Value::VNeu(Neutral::Int(b))) => {
          let val = vneu_or_papp(Neutral::Int(a*b), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        }
        _ => {
          let val = vneu_or_papp(Neutral::Mul(Box::new((val1, val2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        },
      }
    },
    Block::Eqz(idx, case1, case2) => {
      let val = env[idx as usize];
      match &heap[val as usize] {
        Value::VNeu(Neutral::Int(a)) => {
          if *a == 0 {
            eval(store, heap, case1, env, args, cont)
          }
          else {
            eval(store, heap, case2, env, args, cont)
          }
        }
        _ => {
          let val = vneu_or_papp(Neutral::Eqz(Box::new((idx, env, case1, case2))), args, heap);
          match cont {
            None => val,
            Some(mut ctx) => {
              ctx.args.push(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        },
      }
    },
    Block::Impossible => unreachable!(),
  }
}
