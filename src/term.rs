#[derive(Debug, Clone)]
pub enum Term {
  Var(EnvPtr),
  Lam(TermPtr),
  App(TermPtr, TermPtr),
  Ref(TermPtr),
  Opr(Opr),
  Int(i64),
  Impossible,
}

#[derive(Debug, Clone, Copy)]
pub enum Opr {
  Add,
  Mul,
  Sub,
  Eqz,
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

pub type TermPtr = usize;
pub type EnvPtr = usize;
pub type Store = Vec<Term>;

#[inline(always)]
pub fn tvar(idx: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Var(idx));
  store.len()-1
}
#[inline(always)]
pub fn tlam(bod: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Lam(bod));
  store.len()-1
}
#[inline(always)]
pub fn tapp(fun: TermPtr, arg: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::App(fun, arg));
  store.len()-1
}
#[inline(always)]
pub fn tref(idx: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Ref(idx));
  store.len()-1
}
#[inline(always)]
pub fn topr(opr: Opr, store: &mut Store) -> TermPtr {
  store.push(Term::Opr(opr));
  store.len()-1
}
#[inline(always)]
pub fn tint(num: i64, store: &mut Store) -> TermPtr {
  store.push(Term::Int(num));
  store.len()-1
}
#[inline(always)]
pub fn timp(store: &mut Store) -> TermPtr {
  store.push(Term::Impossible);
  store.len()-1
}
