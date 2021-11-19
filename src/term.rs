#[derive(Debug, Clone, Copy)]
pub enum Opr {
  Add,
  Mul,
  Sub,
  Eqz,
}

#[derive(Debug, Clone)]
pub enum Term<'a> {
  Var(usize),
  Lam(&'a Term<'a>),
  App(&'a Term<'a>, &'a Term<'a>),
  Ref(usize),
  Opr(Opr),
  Int(i64),
}

