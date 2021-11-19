use std::{
  rc::Rc,
  vec::Vec,
  cell::RefCell,
};
use im::Vector;
use crate::term::*;

pub type Env<'a> = Vector<Rc<RefCell<Thunk<'a>>>>;
pub type Args<'a> = Vec<Rc<RefCell<Thunk<'a>>>>;
pub type Defs<'a> = Vec<&'a Term<'a>>;

// TODO: implement non-recursive drop
#[derive(Debug, Clone)]
pub enum Value<'a> {
  Papp(Neutral, Args<'a>),
  Lam(&'a Term<'a>, Env<'a>),
}

#[derive(Debug, Clone, Copy)]
pub enum Neutral {
  Var(usize),
  Opr(Opr),
  Int(i64),
}

#[derive(Debug, Clone)]
pub enum Thunk<'a> {
  Sus(&'a Term<'a>, Env<'a>),
  Res(Rc<Value<'a>>),
}

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
pub enum State<'a> {
  Eval(&'a Term<'a>, Env<'a>, Args<'a>),
  Apply(Args<'a>),
  Force(Rc<RefCell<Thunk<'a>>>),
  Update(Rc<RefCell<Thunk<'a>>>),
  Add(Args<'a>),
  Sub(Args<'a>),
  Mul(Args<'a>),
  Eqz(Args<'a>),
  RETURN,
}

#[inline(always)]
pub fn reduce_opr<'a>(cont_stack: &mut Vec<State<'a>>, ret_stack: &mut Vec<Rc<Value<'a>>>, opr: Opr, args: Args<'a>) {
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
pub fn eval<'a>(defs: &Defs<'a>, term: &'a Term<'a>, env: Env<'a>, args: Args<'a>) -> Rc<Value<'a>> {
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
            let term = defs[*idx];
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

pub fn print_int<'a>(val: Rc<Value<'a>>) {
  match &*val {
    Value::Papp(Neutral::Int(num), p_args) if p_args.is_empty() => {
      println!("int {}", num)
    },
    _ => (),
  }
}
