#[derive(Debug, Clone, Copy)]
pub enum Term {
  // Lambda calculus constructs
  Var(EnvPtr),
  Lam(TermPtr),
  App(TermPtr, TermPtr),
  // Reference to global definitions
  Ref(TermPtr),
  // Integers and operations on integers.
  // Notice how operations like `Add` take EnvPtr instead of
  // TermPtr. This is means that when evaluating, it will
  // take the value from the environment, which is already
  // reduced; that is, the arguments are strict. `Eqz` on the
  // other hand, only evaluates the second or third argument
  // when the first is found to be an integer.
  Int(i64),
  Add(EnvPtr, EnvPtr),
  Mul(EnvPtr, EnvPtr),
  Sub(EnvPtr, EnvPtr),
  Eqz(EnvPtr, TermPtr, TermPtr),
  // Dummy value
  Impossible,
}

pub type TermPtr = u32;
pub type EnvPtr = u32;
pub type Store = Vec<Term>;

#[inline(always)]
pub fn tvar(idx: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Var(idx));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tlam(bod: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Lam(bod));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tapp(fun: TermPtr, arg: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::App(fun, arg));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tref(idx: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Ref(idx));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tint(num: i64, store: &mut Store) -> TermPtr {
  store.push(Term::Int(num));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tadd(arg1: EnvPtr, arg2: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Add(arg1, arg2));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tsub(arg1: EnvPtr, arg2: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Sub(arg1, arg2));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tmul(arg1: EnvPtr, arg2: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Mul(arg1, arg2));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn teqz(arg1: EnvPtr, arg2: TermPtr, arg3: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Term::Eqz(arg1, arg2, arg3));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn timp(store: &mut Store) -> TermPtr {
  store.push(Term::Impossible);
  (store.len()-1) as TermPtr
}
