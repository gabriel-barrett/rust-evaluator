use std::{
  vec::Vec,
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

#[derive(Debug, Clone, Copy)]
pub enum Neutral {
  Var(EnvPtr),
  Opr(Opr),
  Int(i64),
}

pub type Heap = Vec<Value>;
pub type ValuePtr = usize;

pub enum State {
  Eval(TermPtr, Env, Args),
  EvalPlus(TermPtr, Env, Args),
  Apply(Args),
  Add(Args),
  Sub(Args),
  Mul(Args),
  Eqz(Args),
  RETURN,
}

#[inline(always)]
pub fn force(cont_stack: &mut Vec<State>, thunk: Thunk) {
  match thunk {
    (sus_term, sus_env) => {
      let term = sus_term;
      let env = sus_env;
      cont_stack.push(State::Eval(term, env, vec![]));
    }
  }
}

#[inline(always)]
pub fn reduce_opr(heap:&mut Heap, cont_stack: &mut Vec<State>, ret_stack: &mut Vec<ValuePtr>, opr: Opr, args: Args) {
  if args.len() < opr_arity(opr) {
    ret_stack.push(papp(Neutral::Opr(opr), args, heap));
  }
  else {
    match opr {
      Opr::Add => {
        let arg2 = args[args.len() - 2].clone();
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Add(args));
        force(cont_stack, arg2);
        force(cont_stack, arg1);
      },
      Opr::Mul => {
        let arg2 = args[args.len() - 2].clone();
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Mul(args));
        force(cont_stack, arg2);
        force(cont_stack, arg1);
      },
      Opr::Sub => {
        let arg2 = args[args.len() - 2].clone();
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Sub(args));
        force(cont_stack, arg2);
        force(cont_stack, arg1);
      },
      Opr::Eqz => {
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Eqz(args));
        force(cont_stack, arg1);
      },
    }
  }
}

#[inline]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr, env: Env, args: Args) -> ValuePtr {
  let mut cont_stack = vec![State::RETURN, State::Eval(term, env, args)];
  let mut ret_stack = vec![];
  loop {
    let state = cont_stack.pop().unwrap();
    match state {
      State::EvalPlus(term, mut env, args) => {
        let value = ret_stack.pop().unwrap();
        env.push_back(value);
        cont_stack.push(State::Eval(term, env, args));
      },
      State::Eval(term, mut env, mut args) => {
        match store[term] {
          Term::App(fun, arg) => {
            let thunk = (arg, env.clone());
            args.push(thunk);
            cont_stack.push(State::Eval(fun, env, args));
          },
          Term::Lam(bod) => {
            if args.len() == 0 {
              ret_stack.push(vlam(bod, env.clone(), heap));
            }
            else {
              let thunk = args.pop().unwrap();
              cont_stack.push(State::EvalPlus(bod, env, args));
              force(&mut cont_stack, thunk);
            }
          },
          Term::Var(idx) => {
            cont_stack.push(State::Apply(args));
            let dep = env.len() - 1 - idx;
            let value = env[dep];
            ret_stack.push(value);
          },
          Term::Opr(opr) => {
            reduce_opr(heap, &mut cont_stack, &mut ret_stack, opr, args)
          },
          Term::Int(int) => {
            ret_stack.push(papp(Neutral::Int(int), args, heap));
          },
          Term::Ref(idx) => {
            env.clear();
            cont_stack.push(State::Eval(idx, env, args))
          },
          Term::Impossible => unreachable!(),
        }
      },
      State::Apply(mut args) => {
        if args.len() == 0 {
          // Does nothing
        }
        else {
          match &heap[ret_stack.pop().unwrap()] {
            Value::Papp(Neutral::Opr(opr), p_args) => {
              args.extend_from_slice(&p_args);
              let opr = *opr;
              reduce_opr(heap, &mut cont_stack, &mut ret_stack, opr, args)
            },
            Value::Papp(neu, p_args) => {
              args.extend_from_slice(&p_args);
              ret_stack.push(papp(*neu, args, heap));
            },
            Value::VLam(bod, lam_env) => {
              let thunk = args.pop().unwrap();
              cont_stack.push(State::EvalPlus(*bod, lam_env.clone(), args));
              force(&mut cont_stack, thunk);
            },
          }
        }
      },
      State::Add(mut args) => {
        let val2 = ret_stack.pop().unwrap();
        let val1 = ret_stack.pop().unwrap();
        match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => {
              args.truncate(args.len() - 2);
              ret_stack.push(papp(Neutral::Int(num1+num2), args, heap))
            }
          _ => ret_stack.push(papp(Neutral::Opr(Opr::Add), args, heap)),
        }
      },
      State::Mul(mut args) => {
        let val2 = ret_stack.pop().unwrap();
        let val1 = ret_stack.pop().unwrap();
        match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => {
              args.truncate(args.len() - 2);
              ret_stack.push(papp(Neutral::Int(num1*num2), args, heap))
            }
          _ => ret_stack.push(papp(Neutral::Opr(Opr::Mul), args, heap)),
        }
      },
      State::Sub(mut args) => {
        let val2 = ret_stack.pop().unwrap();
        let val1 = ret_stack.pop().unwrap();
        match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => {
              args.truncate(args.len() - 2);
              ret_stack.push(papp(Neutral::Int(num1-num2), args, heap))
            }
          _ => ret_stack.push(papp(Neutral::Opr(Opr::Sub), args, heap)),
        }
      },
      State::Eqz(mut args) => {
        let val1 = ret_stack.pop().unwrap();
        match &heap[val1] {
          Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
            args.pop();
            let (case1, env1) = args.pop().unwrap();
            let (case2, env2) = args.pop().unwrap();
            if *num == 0 {
              cont_stack.push(State::Eval(case1, env1, args));
            }
            else {
              cont_stack.push(State::Eval(case2, env2, args));
            }
          },
          _ => ret_stack.push(papp(Neutral::Opr(Opr::Eqz), args, heap)),
        }
      },
      State::RETURN => return ret_stack.pop().unwrap(),
    }
  }
}

pub fn print_int(val: ValuePtr, heap: &mut Heap) {
  match &heap[val] {
    Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
      println!("int {}", num)
    },
    _ => (),
  }
}
