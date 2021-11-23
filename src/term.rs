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

pub type TermPtr = usize;
pub type EnvPtr = usize;
pub type Store = Vec<Term>;

#[inline(always)]
pub fn pvar(idx: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Var(idx));
  store.len()-1
}
#[inline(always)]
pub fn plam(bod: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Lam(bod));
  store.len()-1
}
#[inline(always)]
pub fn papp(fun: TermPtr, arg: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::App(fun, arg));
  store.len()-1
}
#[inline(always)]
pub fn pref(idx: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Ref(idx));
  store.len()-1
}
#[inline(always)]
pub fn popr(opr: Opr, store: &mut Store) -> TermPtr {
  store.push(Term::Opr(opr));
  store.len()-1
}
#[inline(always)]
pub fn pint(num: i64, store: &mut Store) -> TermPtr {
  store.push(Term::Int(num));
  store.len()-1
}
#[inline(always)]
pub fn pimpossible(store: &mut Store) -> TermPtr {
  store.push(Term::Impossible);
  store.len()-1
}
