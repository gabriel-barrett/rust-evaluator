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

#[derive(Debug, Clone)]
pub enum Neutral {
  FVar(usize),
  Int(i64),
  Add(ValuePtr, ValuePtr),
  Mul(ValuePtr, ValuePtr),
  Sub(ValuePtr, ValuePtr),
  Eqz(ValuePtr, Thunk, Thunk),
}

pub type Heap = Vec<Value>;
pub type ValuePtr = usize;

pub enum State {
  Eval(TermPtr, Env, Args),
  EvalPlus(TermPtr, Env, Args),
  Apply(Args),
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
          Term::Int(int) => {
            let value = papp(Neutral::Int(int), args, heap);
            ret_stack.push(value);
          },
          Term::Ref(idx) => {
            env.clear();
            cont_stack.push(State::Eval(idx, env, args))
          },
          Term::Add(val1, val2) => {
            let ptr1 = env[env.len() - 1 - val1];
            let ptr2 = env[env.len() - 1 - val2];
            match (&heap[ptr1], &heap[ptr2]) {
              (Value::Papp(Neutral::Int(num1), p_args1),
               Value::Papp(Neutral::Int(num2), p_args2))
                if p_args1.is_empty() && p_args2.is_empty() => {
                  ret_stack.push(papp(Neutral::Int(num1+num2), args, heap))
                }
              _ => ret_stack.push(papp(Neutral::Add(val1, val2), args, heap)),
            }
          },
          Term::Sub(val1, val2) => {
            let ptr1 = env[env.len() - 1 - val1];
            let ptr2 = env[env.len() - 1 - val2];
            match (&heap[ptr1], &heap[ptr2]) {
              (Value::Papp(Neutral::Int(num1), p_args1),
               Value::Papp(Neutral::Int(num2), p_args2))
                if p_args1.is_empty() && p_args2.is_empty() => {
                  ret_stack.push(papp(Neutral::Int(num1-num2), args, heap))
                }
              _ => ret_stack.push(papp(Neutral::Sub(val1, val2), args, heap)),
            }
          },
          Term::Mul(val1, val2) => {
            let ptr1 = env[env.len() - 1 - val1];
            let ptr2 = env[env.len() - 1 - val2];
            match (&heap[ptr1], &heap[ptr2]) {
              (Value::Papp(Neutral::Int(num1), p_args1),
               Value::Papp(Neutral::Int(num2), p_args2))
                if p_args1.is_empty() && p_args2.is_empty() => {
                  ret_stack.push(papp(Neutral::Int(num1*num2), args, heap))
                }
              _ => ret_stack.push(papp(Neutral::Mul(val1, val2), args, heap)),
            }
          },
          Term::Eqz(val1, case1, case2) => {
            let ptr1 = env[env.len() - 1 - val1];
            match &heap[ptr1] {
              Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
                if *num == 0 {
                  cont_stack.push(State::Eval(case1, env, args));
                }
                else {
                  cont_stack.push(State::Eval(case2, env, args));
                }
              },
              _ => {
                let case1 = (case1, env.clone());
                let case2 = (case2, env.clone());
                ret_stack.push(papp(Neutral::Eqz(val1, case1, case2), args, heap))
              },
            }
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
            Value::Papp(neu, p_args) => {
              args.extend_from_slice(&p_args);
              ret_stack.push(papp(neu.clone(), args, heap));
            },
            Value::VLam(bod, lam_env) => {
              let thunk = args.pop().unwrap();
              cont_stack.push(State::EvalPlus(*bod, lam_env.clone(), args));
              force(&mut cont_stack, thunk);
            },
          }
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
    _ => println!("other"),
  }
}
