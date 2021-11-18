use std::{
  rc::Rc,
  vec::Vec,
  cell::RefCell,
};
use im::Vector;
use crate::term::*;

// TODO: implement non-recursive drop
#[derive(Debug, Clone)]
pub enum Value {
  Papp(Neutral, Args),
  Lam(Rc<Term>, Env),
}
// impl Drop for Value {
//     fn drop(&mut self) {
//     }
// }

#[derive(Debug, Clone, Copy)]
pub enum Neutral {
  Var(usize),
  Opr(Opr),
  Int(i64),
}

#[derive(Debug, Clone)]
pub enum Thunk {
  Sus(Rc<Term>, Env),
  Res(Rc<Value>),
}

pub type Env = Vector<Rc<RefCell<Thunk>>>;
pub type Args = Vec<Rc<RefCell<Thunk>>>;
pub type Defs = Vec<Rc<Term>>;

#[inline(always)]
pub fn opr_arity(opr: Opr) -> usize {
  match opr {
    Opr::Add => 2,
    Opr::Mul => 2,
    Opr::Sub => 2,
    Opr::Eqz => 3,
  }
}

#[allow(non_camel_case_types)]
pub enum State {
  Eval(Rc<Term>, Env, Args),
  Apply(Args),
  Force(Rc<RefCell<Thunk>>),
  Update(Rc<RefCell<Thunk>>),
  Add(Args),
  Sub(Args),
  Mul(Args),
  Eqz(Args),
  RETURN,
}

#[inline(always)]
pub fn reduce_opr(cont_stack: &mut Vec<State>, ret_stack: &mut Vec<Rc<Value>>, opr: Opr, args: Args) {
  if args.len() < opr_arity(opr) {
    ret_stack.push(Rc::new(Value::Papp(Neutral::Opr(opr), args)));
  }
  else {
    match opr {
      Opr::Add => {
        let arg2 = args[args.len() - 2].clone();
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Add(args));
        cont_stack.push(State::Force(arg2));
        cont_stack.push(State::Force(arg1));
      },
      Opr::Mul => {
        let arg2 = args[args.len() - 2].clone();
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Mul(args));
        cont_stack.push(State::Force(arg2));
        cont_stack.push(State::Force(arg1));
      },
      Opr::Sub => {
        let arg2 = args[args.len() - 2].clone();
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Sub(args));
        cont_stack.push(State::Force(arg2));
        cont_stack.push(State::Force(arg1));
      },
      Opr::Eqz => {
        let arg1 = args[args.len() - 1].clone();
        cont_stack.push(State::Eqz(args));
        cont_stack.push(State::Force(arg1));
      },
    }
  }
}

#[inline]
pub fn eval(defs: &Defs, term: Rc<Term>, env: Env, args: Args) -> Rc<Value> {
  let mut cont_stack = vec![State::RETURN, State::Eval(term, env, args)];
  let mut ret_stack = vec![];
  loop {
    let state = cont_stack.pop().unwrap();
    match state {
      State::Eval(term, mut env, mut args) => {
        match &*term {
          Term::App(fun, arg) => {
            let thunk = Rc::new(RefCell::new(Thunk::Sus(arg.clone(), env.clone())));
            args.push(thunk);
            cont_stack.push(State::Eval(fun.clone(), env, args));
          },
          Term::Lam(bod) => {
            if args.len() == 0 {
              ret_stack.push(Rc::new(Value::Lam(bod.clone(), env.clone())));
            }
            else {
              let thunk = args.pop().unwrap();
              env.push_back(thunk);
              cont_stack.push(State::Eval(bod.clone(), env, args))
            }
          },
          Term::Var(idx) => {
            cont_stack.push(State::Apply(args));
            let dep = env.len() - 1 - idx;
            let thunk = env[dep].clone();
            cont_stack.push(State::Force(thunk));
          },
          Term::Opr(opr) => {
            reduce_opr(&mut cont_stack, &mut ret_stack, *opr, args)
          },
          Term::Int(int) => {
            ret_stack.push(Rc::new(Value::Papp(Neutral::Int(*int), args)));
          },
          Term::Ref(idx) => {
            env.clear();
            let term = defs[*idx].clone();
            cont_stack.push(State::Eval(term, env, args))
          },
        }
      },
      State::Apply(mut args) => {
        if args.len() == 0 {
          // Does nothing
        }
        else {
          match &*ret_stack.pop().unwrap() {
            Value::Papp(Neutral::Opr(opr), p_args) => {
              args.extend_from_slice(p_args);
              reduce_opr(&mut cont_stack, &mut ret_stack, *opr, args)
            },
            Value::Papp(neu, p_args) => {
              args.extend_from_slice(p_args);
              ret_stack.push(Rc::new(Value::Papp(*neu, args)));
            },
            Value::Lam(bod, lam_env) => {
              let thunk = args.pop().unwrap();
              let mut env = lam_env.clone();
              env.push_back(thunk);
              cont_stack.push(State::Eval(bod.clone(), env, args));
            },
          }
        }
      },
      State::Force(thunk) => {
        let borrow = thunk.borrow();
        match &*borrow {
          Thunk::Sus(sus_term, sus_env) => {
            let term = sus_term.clone();
            let env = sus_env.clone();
            drop(borrow);
            cont_stack.push(State::Update(thunk));
            cont_stack.push(State::Eval(term, env, vec![]));
          },
          Thunk::Res(val) => {
            ret_stack.push(val.clone());
          },
        }
      },
      State::Update(thunk) => {
        let mut mut_ref = thunk.borrow_mut();
        let value = ret_stack.last().unwrap();
        *mut_ref = Thunk::Res(value.clone());
        // Stack overflowing because of recursive drop.
      }
      State::Add(mut args) => {
        let val2 = ret_stack.pop().unwrap();
        let val1 = ret_stack.pop().unwrap();
        match (&*val1, &*val2) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => {
              args.truncate(args.len() - 2);
              ret_stack.push(Rc::new(Value::Papp(Neutral::Int(num1+num2), args)))
            }
          _ => ret_stack.push(Rc::new(Value::Papp(Neutral::Opr(Opr::Add), args))),
        }
      },
      State::Mul(mut args) => {
        let val2 = ret_stack.pop().unwrap();
        let val1 = ret_stack.pop().unwrap();
        match (&*val1, &*val2) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => {
              args.truncate(args.len() - 2);
              ret_stack.push(Rc::new(Value::Papp(Neutral::Int(num1*num2), args)))
            }
          _ => ret_stack.push(Rc::new(Value::Papp(Neutral::Opr(Opr::Mul), args))),
        }
      },
      State::Sub(mut args) => {
        let val2 = ret_stack.pop().unwrap();
        let val1 = ret_stack.pop().unwrap();
        match (&*val1, &*val2) {
          (Value::Papp(Neutral::Int(num1), p_args1),
           Value::Papp(Neutral::Int(num2), p_args2))
            if p_args1.is_empty() && p_args2.is_empty() => {
              args.truncate(args.len() - 2);
              ret_stack.push(Rc::new(Value::Papp(Neutral::Int(num1-num2), args)))
            }
          _ => ret_stack.push(Rc::new(Value::Papp(Neutral::Opr(Opr::Sub), args))),
        }
      },
      State::Eqz(mut args) => {
        let val1 = ret_stack.pop().unwrap();
        match &*val1 {
          Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
            args.pop();
            let case1 = args.pop().unwrap();
            let case2 = args.pop().unwrap();
            if *num == 0 {
              cont_stack.push(State::Apply(args));
              cont_stack.push(State::Force(case1));
            }
            else {
              cont_stack.push(State::Apply(args));
              cont_stack.push(State::Force(case2));
            }
          },
          _ => ret_stack.push(Rc::new(Value::Papp(Neutral::Opr(Opr::Eqz), args))),
        }
      },
      State::RETURN => return ret_stack.pop().unwrap(),
    }
  }
}

pub fn print_int(val: Rc<Value>) {
  match &*val {
    Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
      println!("int {}", num)
    },
    _ => (),
  }
}
