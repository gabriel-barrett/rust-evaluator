use std::{
  vec::Vec,
  boxed::Box,
};
use tailcall::tailcall;
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

pub type Env = Vector<ValuePtr>;
pub type Args = Vec<ValuePtr>;

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

pub type Continuation = Option<Box<Node>>;

pub struct Node {
  term: TermPtr,
  env: Env,
  args: Args,
  cont: Continuation,
}

#[tailcall]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, mut env: Env, mut args: Args, mut cont: Continuation) -> ValuePtr {
  match store[term] {
    Term::App(fun, arg) => {
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
    Term::Lam(bod) => {
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
    Term::Var(idx) => {
      let val = env[idx];
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
        match &heap[val] {
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
        }
      }
    },
    Term::Int(int) => {
      let val = papp(Neutral::Int(int), args, heap);
      match cont {
        None => val,
        Some(mut ctx) => {
          ctx.args.push(val);
          eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
        },
      }
    },
    Term::Ref(idx) => {
      eval(store, heap, idx, Vector::new(), args, cont)
    },
    Term::Add(idx1, idx2) => {
      let val1 = env[idx1];
      let val2 = env[idx2];
      match (&heap[val1], &heap[val2]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a+b), args, heap);
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.args.push(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        _ => {
          let val = papp(Neutral::Add(Box::new((val1, val2))), args, heap);
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
    Term::Sub(idx1, idx2) => {
      let val1 = env[idx1];
      let val2 = env[idx2];
      match (&heap[val1], &heap[val2]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a-b), args, heap);
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.args.push(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        _ => {
          let val = papp(Neutral::Sub(Box::new((val1, val2))), args, heap);
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
    Term::Mul(idx1, idx2) => {
      let val1 = env[idx1];
      let val2 = env[idx2];
      match (&heap[val1], &heap[val2]) {
        (Value::Papp(Neutral::Int(a), args_a),
         Value::Papp(Neutral::Int(b), args_b))
          if args_a.is_empty() && args_b.is_empty() => {
            let val = papp(Neutral::Int(a*b), args, heap);
            match cont {
              None => val,
              Some(mut ctx) => {
                ctx.args.push(val);
                eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
              },
            }
          }
        _ => {
          let val = papp(Neutral::Mul(Box::new((val1, val2))), args, heap);
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
    Term::Eqz(idx, case1, case2) => {
      let val = env[idx];
      match &heap[val] {
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
              ctx.args.push(val);
              eval(store, heap, ctx.term, ctx.env, ctx.args, ctx.cont)
            },
          }
        },
      }
    },
    Term::Impossible => unreachable!(),
  }
}
