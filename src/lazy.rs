use std::{
  vec::Vec,
  boxed::Box,
};
use tailcall::trampoline;
use im::Vector;
use crate::block::*;

#[derive(Debug, Clone)]
pub enum Value {
  VNeu(Neutral),
  Papp(Neutral, Args),
  VLam(TermPtr, Env),
  SLam(TermPtr, Env),
}

#[derive(Debug, Clone)]
pub enum Neutral {
  FVar(u32),
  Int(i64),
  Add(Box<(ThunkPtr, ThunkPtr)>),
  Mul(Box<(ThunkPtr, ThunkPtr)>),
  Sub(Box<(ThunkPtr, ThunkPtr)>),
  Eqz(Box<(ThunkPtr, Env, TermPtr, TermPtr)>),
}

#[derive(Debug, Clone)]
pub enum Thunk {
  Sus(TermPtr, Env),
  Res(Value),
  Blackhole,
}
pub type Env = Vector<ThunkPtr>;
pub type Args = Vec<ThunkPtr>;

pub type Continuation = Option<Box<Node>>;

pub enum Node {
  EXTEVAL(TermPtr, Env, ThunkPtr, Args, Continuation),
  APPLY(Args, Continuation),
  UPDATE(ThunkPtr, Continuation),
}

#[inline(always)]
pub fn new_thunk(arg: TermPtr, env: Env, heap: &mut Heap) -> ThunkPtr {
  heap.push(Thunk::Sus(arg, env));
  (heap.len()-1) as ThunkPtr
}

pub type Heap = Vec<Thunk>;
pub type ThunkPtr = u32;

#[inline(always)]
pub fn vneu_or_papp(neu: Neutral, args: Args) -> Value {
  if args.len() == 0 {
    Value::VNeu(neu)
  }
  else {
    Value::Papp(neu, args)
  }
}

#[inline(always)]
fn cont_or_ret<'a>(
  store: &'a Store, heap: &'a mut Heap, mut val: Value, mut cont: Continuation
) -> trampoline::Next<(&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation), Value> {
  loop {
    match cont {
      None => return trampoline::Finish(val),
      Some(ptr) => {
	match *ptr {
	  Node::EXTEVAL(trm, mut env, arg, args, cont) => {
	    env.push_front(arg);
	    return trampoline::Recurse((store, heap, trm, env, args, cont))
	  },
	  Node::APPLY(mut args, new_cont) => {
	    if args.is_empty() {
	      cont = new_cont;
	    }
	    else {
	      match val {
		Value::Papp(neu, p_args) => {
		  args.extend_from_slice(&p_args);
		  val = Value::Papp(neu.clone(), args);
		  cont = new_cont;
		}
		Value::SLam(bod, env) => {
		  let term = bod;
		  let mut env = env.clone();
		  let arg = args.pop().unwrap();
		  env.push_front(arg);
		  return trampoline::Recurse((store, heap, term, env, args, new_cont))
		},
		Value::VLam(bod, env) => {
		  let term = bod;
		  let mut env = env.clone();
		  let arg = args.pop().unwrap();
		  env.push_front(arg);
		  return trampoline::Recurse((store, heap, term, env, args, new_cont))
		},
		Value::VNeu(neu) => {
		  val = vneu_or_papp(neu.clone(), args);
		  cont = new_cont;
		}
	      }
	    }
	  },
	  Node::UPDATE(thunk, new_cont) => {
	    heap[thunk as usize] = Thunk::Res(val.clone());
	    cont = new_cont;
	  },
	}
      }
    }
  }
}

#[inline(always)]
pub fn force<'a>(
  store: &'a Store, heap: &'a mut Heap, thunk: ThunkPtr, mut cont: Continuation
) -> trampoline::Next<(&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation), Value> {
  match &heap[thunk as usize] {
    Thunk::Res(val) => {
      let val = val.clone();
      cont_or_ret(store, heap, val, cont)
    },
    Thunk::Sus(..) => {
      let mut replace = Thunk::Blackhole;
      std::mem::swap(&mut heap[thunk as usize], &mut replace);
      match replace {
	Thunk::Sus(trm, env) => {
	  cont = Some(Box::new(Node::UPDATE(thunk, cont)));
	  trampoline::Recurse((store, heap, trm, env, vec![], cont))
	},
	_ => unreachable!(),
      }
    },
    Thunk::Blackhole => unreachable!(),
  }
}

pub fn eval_step<'a>(
  (store, heap, term, mut env, mut args, mut cont): (&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation)
) -> trampoline::Next<(&'a Store, &'a mut Heap, TermPtr, Env, Args, Continuation), Value> {
  match store[term as usize] {
    Block::App(fun, arg) => {
      args.push(new_thunk(arg, env.clone(), heap));
      trampoline::Recurse((store, heap, fun, env, args, cont))
    },
    Block::SLam(bod) => {
      match args.pop() {
        Some(arg) => {
	  cont = Some(
	    Box::new(Node::EXTEVAL(
	      bod,
	      env,
	      arg,
	      args,
	      cont
	    ))
	  );
	  force(store, heap, arg, cont)
        },
        None => {
          let val = Value::SLam(bod, env);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Lam(bod) => {
      match args.pop() {
        Some(arg) => {
          env.push_front(arg);
	  trampoline::Recurse((store, heap, bod, env, args, cont))
        },
        None => {
          let val = Value::VLam(bod, env);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Var(idx) => {
      cont = Some(Box::new(Node::APPLY(args, cont)));
      force(store, heap, env[idx as usize], cont)
    },
    Block::Int(int) => {
      let val = vneu_or_papp(Neutral::Int(int), args);
      cont_or_ret(store, heap, val, cont)
    },
    Block::Ref(idx) => {
      trampoline::Recurse((store, heap, idx, env, args, cont))
    },
    Block::Add(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Thunk::Res(Value::VNeu(Neutral::Int(a))),
         Thunk::Res(Value::VNeu(Neutral::Int(b)))) => {
          let val = vneu_or_papp(Neutral::Int(a+b), args);
	  cont_or_ret(store, heap, val, cont)
        }
        _ => {
          let val = vneu_or_papp(Neutral::Add(Box::new((val1, val2))), args);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Sub(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Thunk::Res(Value::VNeu(Neutral::Int(a))),
         Thunk::Res(Value::VNeu(Neutral::Int(b)))) => {
          let val = vneu_or_papp(Neutral::Int(a-b), args);
	  cont_or_ret(store, heap, val, cont)
        }
        _ => {
          let val = vneu_or_papp(Neutral::Sub(Box::new((val1, val2))), args);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Mul(idx1, idx2) => {
      let val1 = env[idx1 as usize];
      let val2 = env[idx2 as usize];
      match (&heap[val1 as usize], &heap[val2 as usize]) {
        (Thunk::Res(Value::VNeu(Neutral::Int(a))),
         Thunk::Res(Value::VNeu(Neutral::Int(b)))) => {
          let val = vneu_or_papp(Neutral::Int(a*b), args);
	  cont_or_ret(store, heap, val, cont)
        }
        _ => {
          let val = vneu_or_papp(Neutral::Mul(Box::new((val1, val2))), args);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Eqz(idx, case1, case2) => {
      let val = env[idx as usize];
      match &heap[val as usize] {
        Thunk::Res(Value::VNeu(Neutral::Int(a))) => {
          if *a == 0 {
            trampoline::Recurse((store, heap, case1, env, args, cont))
          }
          else {
            trampoline::Recurse((store, heap, case2, env, args, cont))
          }
        }
        _ => {
          let val = vneu_or_papp(Neutral::Eqz(Box::new((idx, env, case1, case2))), args);
	  cont_or_ret(store, heap, val, cont)
        },
      }
    },
    Block::Impossible => unreachable!(),
  }
}

pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, env: Env, args: Args) -> Value {
  trampoline::run(eval_step, (store, heap, term, env, args, None))
}
