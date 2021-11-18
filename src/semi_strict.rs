use std::{
  rc::Rc,
  vec::Vec,
};
use im::Vector;
use crate::term::*;

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

pub type Thunk = (Rc<Term>, Env);
pub type Env = Vector<Rc<Value>>;
pub type Args = Vec<Rc<Thunk>>;
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
  EvalPlus(Rc<Term>, Env, Args),
  Apply(Args),
  Add(Args),
  Sub(Args),
  Mul(Args),
  Eqz(Args),
  RETURN,
}

#[inline(always)]
pub fn force(cont_stack: &mut Vec<State>, thunk: Rc<Thunk>) {
  match &*thunk {
    (sus_term, sus_env) => {
      let term = sus_term.clone();
      let env = sus_env.clone();
      cont_stack.push(State::Eval(term, env, vec![]));
    }
  }
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
pub fn eval(defs: &Defs, term: Rc<Term>, env: Env, args: Args) -> Rc<Value> {
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
        match &*term {
          Term::App(fun, arg) => {
            let thunk = Rc::new((arg.clone(), env.clone()));
            args.push(thunk);
            cont_stack.push(State::Eval(fun.clone(), env, args));
          },
          Term::Lam(bod) => {
            if args.len() == 0 {
              ret_stack.push(Rc::new(Value::Lam(bod.clone(), env.clone())));
            }
            else {
              let thunk = args.pop().unwrap();
              cont_stack.push(State::EvalPlus(bod.clone(), env, args));
              force(&mut cont_stack, thunk);
            }
          },
          Term::Var(idx) => {
            cont_stack.push(State::Apply(args));
            let dep = env.len() - 1 - idx;
            let value = env[dep].clone();
            ret_stack.push(value);
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
              cont_stack.push(State::EvalPlus(bod.clone(), lam_env.clone(), args));
              force(&mut cont_stack, thunk);
            },
          }
        }
      },
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
              force(&mut cont_stack, case1);
            }
            else {
              cont_stack.push(State::Apply(args));
              force(&mut cont_stack, case2);
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
