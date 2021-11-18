use std::{
  rc::Rc,
};
use im::Vector;

use evaluator::lazy;
use evaluator::semi_strict;
use evaluator::term::*;

macro_rules! app {
    ($fun:expr, $arg:expr) => {
        Term::App(Rc::new($fun), Rc::new($arg))
    };
}

macro_rules! lam {
    ($bod:expr) => {
        Term::Lam(Rc::new($bod))
    };
}

fn main() {
  let cons_t = Rc::new(lam!(lam!(lam!(lam!(app!(app!(Term::Var(0), Term::Var(3)), app!(app!(Term::Var(2), Term::Var(1)), Term::Var(0))))))));
  let nil_t  = Rc::new(lam!(lam!(Term::Var(1))));
  let repeat_t = Rc::new(lam!(lam!(app!(app!(app!(Term::Opr(Opr::Eqz), Term::Var(1)), Term::Ref(1)), app!(app!(Term::Ref(0), Term::Var(0)), app!(app!(Term::Ref(2), app!(app!(Term::Opr(Opr::Sub), Term::Var(1)), Term::Int(1))), Term::Var(0)))))));
  let sum_t = Rc::new(lam!(app!(app!(Term::Var(0), Term::Int(0)), lam!(lam!(app!(app!(Term::Opr(Opr::Add), Term::Var(1)), Term::Var(0)))))));
  let val_t = Rc::new(Term::Int(12000));
  let list_t = Rc::new(app!(app!(Term::Ref(2), Term::Ref(4)), Term::Int(1)));
  let main_t = Rc::new(app!(Term::Ref(3), Term::Ref(5)));
  let defs = vec![cons_t, nil_t, repeat_t, sum_t, val_t, list_t, main_t];

  let env = Vector::new();
  let args = vec![];
  // lazy::print_int(lazy::eval(&defs, defs[6].clone(), env, args))
  semi_strict::print_int(semi_strict::eval(&defs, defs[6].clone(), env, args))
}
