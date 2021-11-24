use std::{
  mem,
  vec::Vec,
  boxed::Box,
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
  Add(Box<(ValuePtr, ValuePtr)>),
  Mul(Box<(ValuePtr, ValuePtr)>),
  Sub(Box<(ValuePtr, ValuePtr)>),
  Eqz(Box<(ValuePtr, Thunk, Thunk)>),
}

pub type Heap = Vec<Value>;
pub type ValuePtr = usize;

pub type State = (bool, TermPtr, Env);

#[inline]
pub fn eval(store: &Store, heap: &mut Heap, term: TermPtr) -> ValuePtr {
  let mut node = term;
  let mut env: Env = Vector::new();
  let mut stack = vec![];
  loop {
    match store[node] {
      Term::App(fun, arg) => {
        stack.push((true, arg, env.clone()));
        node = fun;
      },
      Term::Lam(bod) => {
        match stack.last_mut() {
          Some((is_arg, exp, exp_env)) => {
            if *is_arg {
              node = *exp;
              *is_arg = false;
              *exp = bod;
              mem::swap(exp_env, &mut env);
            }
            else {
              node = *exp;
              let value = vlam(bod, env.clone(), heap);
              mem::swap(exp_env, &mut env);
              env.push_back(value);
              stack.pop();
            }
          },
          None => {
            return vlam(bod, env, heap);
          },
        }
      },
      Term::Var(idx) => {
        let value = env[env.len() - 1 - idx];
        match stack.last_mut() {
          Some((is_arg, exp, exp_env)) => {
            if *is_arg {
              match &heap[value] {
                Value::Papp(neu, p_args) => {
                  let mut args = p_args.clone();
                  loop {
                    match stack.pop() {
                      Some((is_arg, exp, mut exp_env)) => {
                        if is_arg {
                          args.push((exp, exp_env));
                        }
                        else {
                          node = exp;
                          mem::swap(&mut exp_env, &mut env);
                          env.push_back(papp(neu.clone(), args, heap));
                          break
                        }
                      },
                      None => return papp(neu.clone(), args, heap),
                    }
                  }
                },
                Value::VLam(bod, lam_env) => {
                  node = *exp;
                  *is_arg = false;
                  *exp = *bod;
                  mem::swap(exp_env, &mut env);
                  *exp_env = lam_env.clone();
                },
              }
            }
            else {
              node = *exp;
              mem::swap(exp_env, &mut env);
              env.push_back(value);
              stack.pop();
            }
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
        loop {
          match stack.pop() {
            Some((is_arg, exp, mut exp_env)) => {
              if is_arg {
                args.push((exp, exp_env));
              }
              else {
                node = exp;
                mem::swap(&mut exp_env, &mut env);
                env.push_back(papp(neu, args, heap));
                break
              }
            },
            None => return papp(neu, args, heap),
          }
        }
      },
      Term::Add(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1];
        let val2 = env[env.len() - 1 - idx2];
        let neu = match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1+num2),
          _ => Neutral::Add(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        loop {
          match stack.pop() {
            Some((is_arg, exp, mut exp_env)) => {
              if is_arg {
                args.push((exp, exp_env));
              }
              else {
                node = exp;
                mem::swap(&mut exp_env, &mut env);
                env.push_back(papp(neu, args, heap));
                break
              }
            },
            None => return papp(neu, args, heap),
          }
        }
      },
      Term::Mul(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1];
        let val2 = env[env.len() - 1 - idx2];
        let neu = match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1*num2),
          _ => Neutral::Mul(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        loop {
          match stack.pop() {
            Some((is_arg, exp, mut exp_env)) => {
              if is_arg {
                args.push((exp, exp_env));
              }
              else {
                node = exp;
                mem::swap(&mut exp_env, &mut env);
                env.push_back(papp(neu, args, heap));
                break
              }
            },
            None => return papp(neu, args, heap),
          }
        }
      },
      Term::Sub(idx1, idx2) => {
        let val1 = env[env.len() - 1 - idx1];
        let val2 = env[env.len() - 1 - idx2];
        let neu = match (&heap[val1], &heap[val2]) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => Neutral::Int(num1-num2),
          _ => Neutral::Sub(Box::new((idx1, idx2))),
        };
        let mut args = vec![];
        loop {
          match stack.pop() {
            Some((is_arg, exp, mut exp_env)) => {
              if is_arg {
                args.push((exp, exp_env));
              }
              else {
                node = exp;
                mem::swap(&mut exp_env, &mut env);
                env.push_back(papp(neu, args, heap));
                break
              }
            },
            None => return papp(neu, args, heap),
          }
        }
      },
      Term::Eqz(idx, case1, case2) => {
        let val = env[env.len() - 1 - idx];
        match &heap[val] {
          Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
            if *num == 0 {
              node = case1;
            }
            else {
              node = case2;
            }
          },
          _ => {
            let case1 = (case1, env.clone());
            let case2 = (case2, env.clone());
            let neu = Neutral::Eqz(Box::new((idx, case1, case2)));
            let mut args = vec![];
            loop {
              match stack.pop() {
                Some((is_arg, exp, mut exp_env)) => {
                  if is_arg {
                    args.push((exp, exp_env));
                  }
                  else {
                    node = exp;
                    mem::swap(&mut exp_env, &mut env);
                    env.push_back(papp(neu, args, heap));
                    break
                  }
                },
                None => return papp(neu, args, heap),
              }
            }
          },
        }
      },
      Term::Impossible => {
        unreachable!()
      },
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
