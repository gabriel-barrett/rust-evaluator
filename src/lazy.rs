use std::{
  vec::Vec,
  boxed::Box,
};
use im::Vector;
use crate::block::*;

#[derive(Debug, Clone)]
pub enum Thunk {
  Sus(TermPtr, Env),
  Res(Value),
  Blackhole,
}
pub type Env = Vector<ThunkPtr>;
pub type Args = Vec<ThunkPtr>;

#[derive(Debug, Clone)]
pub enum Value {
  Papp(Neutral, Args),
  VLam(TermPtr, Box<Env>),
  SLam(TermPtr, Box<Env>),
}

#[inline(always)]
pub fn papp(neu: Neutral, args: Args, heap: &mut Heap) -> ThunkPtr {
  heap.push(Thunk::Res(Value::Papp(neu, args)));
  (heap.len()-1) as ThunkPtr
}

#[inline(always)]
pub fn slam(term: TermPtr, env: Env, heap: &mut Heap) -> ThunkPtr {
  heap.push(Thunk::Res(Value::SLam(term, Box::new(env))));
  (heap.len()-1) as ThunkPtr
}

#[inline(always)]
pub fn vlam(term: TermPtr, env: Env, heap: &mut Heap) -> ThunkPtr {
  heap.push(Thunk::Res(Value::VLam(term, Box::new(env))));
  (heap.len()-1) as ThunkPtr
}

#[inline(always)]
pub fn new_thunk(term: TermPtr, env: Env, heap: &mut Heap) -> ThunkPtr {
  heap.push(Thunk::Sus(term, env));
  (heap.len()-1) as ThunkPtr
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

pub type Heap = Vec<Thunk>;
pub type ThunkPtr = u32;

#[derive(Debug, Clone, Copy)]
pub enum Kind {
  Upd,
  Arg,
  Ext,
}

#[derive(Debug, Clone)]
pub struct State {
  kind: Kind,
  thunk: ThunkPtr
}

#[inline]
pub fn eval(store: &Store, heap: &mut Heap, mut node: TermPtr) -> ThunkPtr {
  macro_rules! apply {
    ($heap:ident, $stack:ident, $node:ident, $env:ident, $neu:expr, $args:ident) => {
      loop {
        match $stack.pop() {
          Some(State { kind: Kind::Arg, thunk }) => {
            $args.push(thunk);
          },
          Some(State { kind: Kind::Upd, thunk }) => {
	    let val = Value::Papp($neu, $args);
	    heap[thunk as usize] = Thunk::Res(val);
	    break;
          },
          Some(State { kind: Kind::Ext, thunk }) => {
	    let mut replace = Thunk::Res(Value::Papp($neu, $args));
	    std::mem::swap(&mut $heap[thunk as usize], &mut replace);
	    match replace {
	      Thunk::Sus(term, new_env) => {
		$node = term;
		$env = new_env;
		$env.push_front(thunk);
		break;
	      }
	      _ => unreachable!(),
	    }
	  }
          None => return papp($neu, $args, $heap),
        }
      }
    }
  }

  let mut env: Env = Vector::new();
  let mut stack = vec![];
  loop {
    match store[node as usize] {
      Block::App(fun, arg) => {
	let thunk = new_thunk(arg, env.clone(), heap);
        stack.push(State { kind: Kind::Arg, thunk: thunk });
        node = fun;
      },
      Block::SLam(bod) => {
        match stack.pop() {
          Some(State { kind: Kind::Arg, thunk }) => {
	    let borrow = &mut heap[thunk as usize];
	    match borrow {
	      Thunk::Sus(..) => {
		let mut replace = Thunk::Blackhole;
		std::mem::swap(borrow, &mut replace);
		match replace {
		  Thunk::Sus(term, mut new_env) => {
		    std::mem::swap(&mut new_env, &mut env);
		    let new_thunk = new_thunk(bod, new_env, heap);
		    stack.push(State { kind: Kind::Ext, thunk: new_thunk });
		    stack.push(State { kind: Kind::Upd, thunk: thunk });
		    node = term;
		    
		  }
		  _ => unreachable!()
		}
	      },
	      Thunk::Res(..) => {
		env.push_front(thunk);
		node = bod;
	      },
	      Thunk::Blackhole => unreachable!()
	    }
          },
          Some(State { kind: Kind::Upd, thunk }) => {
	    let val = Value::SLam(bod, Box::new(env.clone()));
	    heap[thunk as usize] = Thunk::Res(val);
          },
          Some(State { kind: Kind::Ext, thunk }) => {
	    let mut replace = Thunk::Res(Value::SLam(bod, Box::new(env.clone())));
	    std::mem::swap(&mut heap[thunk as usize], &mut replace);
	    match replace {
	      Thunk::Sus(term, new_env) => {
		node = term;
		env = new_env;
		env.push_front(thunk);
	      }
	      _ => unreachable!(),
	    }
	  }
          None => {
            return vlam(bod, env, heap);
          },
        }
      }
      Block::Lam(bod) => {
        match stack.pop() {
          Some(State { kind: Kind::Arg, thunk }) => {
	    env.push_front(thunk);
            node = bod;
          },
          Some(State { kind: Kind::Upd, thunk }) => {
	    let val = Value::VLam(bod, Box::new(env.clone()));
	    heap[thunk as usize] = Thunk::Res(val);
          },
          Some(State { kind: Kind::Ext, thunk }) => {
	    let mut replace = Thunk::Res(Value::VLam(bod, Box::new(env.clone())));
	    std::mem::swap(&mut heap[thunk as usize], &mut replace);
	    match replace {
	      Thunk::Sus(term, new_env) => {
		node = term;
		env = new_env;
		env.push_front(thunk);
	      }
	      _ => unreachable!(),
	    }
	  }
          None => {
            return vlam(bod, env, heap);
          },
        }
      },
      Block::Var(idx) => {
        let thunk = env[idx as usize];
	let borrow = &mut heap[thunk as usize];
	match borrow {
	  Thunk::Sus(..) => {
	    let mut replace = Thunk::Blackhole;
	    std::mem::swap(borrow, &mut replace);
	    let (term, new_env) = match replace {
	      Thunk::Sus(term, env) => (term, env),
	      _ => unreachable!()
	    };
	    node = term;
	    env = new_env;
	    stack.push(State { kind: Kind::Upd, thunk })
	  },
	  Thunk::Res(value) => {
            match stack.pop() {
              Some(State { kind: Kind::Arg, thunk }) => {
                match value {
		  Value::SLam(bod, lam_env) => {
		    let bod = *bod;
		    let lam_env = (**lam_env).clone();
		    let borrow = &mut heap[thunk as usize];
		    match borrow {
		      Thunk::Sus(..) => {
			let mut replace = Thunk::Blackhole;
			std::mem::swap(borrow, &mut replace);
			match replace {
			  Thunk::Sus(term, mut new_env) => {
			    std::mem::swap(&mut new_env, &mut env);
			    new_env = lam_env;
			    let new_thunk = new_thunk(bod, new_env, heap);
			    stack.push(State { kind: Kind::Ext, thunk: new_thunk });
			    stack.push(State { kind: Kind::Upd, thunk: thunk });
			    node = term;
			    
			  }
			  _ => unreachable!()
			}
		      },
		      Thunk::Res(..) => {
			node = bod;
			env = lam_env;
			env.push_front(thunk);
		      },
		      Thunk::Blackhole => unreachable!()
		    }
		  }
                  Value::VLam(bod, lam_env) => {
		    node = *bod;
		    env = (**lam_env).clone();
		    env.push_front(thunk);
                  },
                  Value::Papp(neu, p_args) => {
                    let mut args = p_args.clone();
                    apply!(heap, stack, node, env, neu.clone(), args);
                  },
                }
              },
              Some(State { kind: Kind::Upd, thunk }) => {
		let val = value.clone();
		heap[thunk as usize] = Thunk::Res(val);
              },
              Some(State { kind: Kind::Ext, thunk: cont_thunk }) => {
		let mut replace = Thunk::Blackhole;
		std::mem::swap(&mut heap[cont_thunk as usize], &mut replace);
		match replace {
		  Thunk::Sus(term, new_env) => {
		    node = term;
		    env = new_env;
		    env.push_front(thunk);
		  }
		  _ => unreachable!(),
		}
	      }
              None => {
		return thunk;
              },
            }
	    
	  },
	  Thunk::Blackhole => panic!("Infinite loop found"),
	}
      },
      Block::Ref(idx) => {
        node = idx;
      },
      Block::Int(num) => {
        let neu = Neutral::Int(num);
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Block::Add(idx1, idx2) => {
        let val1 = env[idx1 as usize];
        let val2 = env[idx2 as usize];
        let neu = match (&heap[val1 as usize], &heap[val2 as usize]) {
          (Thunk::Res(Value::Papp(Neutral::Int(num1), p_args1)),
           Thunk::Res(Value::Papp(Neutral::Int(num2), p_args2)))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1+num2),
          _ => Neutral::Add(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Block::Mul(idx1, idx2) => {
        let val1 = env[idx1 as usize];
        let val2 = env[idx2 as usize];
        let neu = match (&heap[val1 as usize], &heap[val2 as usize]) {
          (Thunk::Res(Value::Papp(Neutral::Int(num1), p_args1)),
           Thunk::Res(Value::Papp(Neutral::Int(num2), p_args2)))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1*num2),
          _ => Neutral::Mul(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Block::Sub(idx1, idx2) => {
        let val1 = env[idx1 as usize];
        let val2 = env[idx2 as usize];
        let neu = match (&heap[val1 as usize], &heap[val2 as usize]) {
          (Thunk::Res(Value::Papp(Neutral::Int(num1), p_args1)),
           Thunk::Res(Value::Papp(Neutral::Int(num2), p_args2)))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1-num2),
          _ => Neutral::Sub(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        apply!(heap, stack, node, env, neu, args);
      },
      Block::Eqz(idx, case1, case2) => {
        let val = env[idx as usize];
        match &heap[val as usize] {
          Thunk::Res(Value::Papp(Neutral::Int(num), p_args)) if p_args.is_empty() => {
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
      Block::Impossible => {
        unreachable!()
      },
    }
  }
}
