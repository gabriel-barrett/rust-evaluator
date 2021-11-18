use std::{
  rc::Rc,
};

#[derive(Debug, Clone, Copy)]
pub enum Opr {
  Add,
  Mul,
  Sub,
  Eqz,
}

#[derive(Debug, Clone)]
pub enum Term {
  Var(usize),
  Lam(Rc<Term>),
  App(Rc<Term>, Rc<Term>),
  Ref(usize),
  Opr(Opr),
  Int(i64),
}

