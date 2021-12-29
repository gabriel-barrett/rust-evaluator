use crate::term::*;

#[derive(Debug, Clone)]
pub enum Block {
  // Lambda calculus constructs
  Var(EnvPtr),
  Lam(TermPtr),
  SLam(TermPtr),
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
pub type Store = Vec<Block>;

#[inline(always)]
pub fn tvar(idx: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Block::Var(idx));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tref(idx: TermPtr, store: &mut Store) -> TermPtr {
  store.push(Block::Ref(idx));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tint(num: i64, store: &mut Store) -> TermPtr {
  store.push(Block::Int(num));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tadd(arg1: EnvPtr, arg2: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Block::Add(arg1, arg2));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tsub(arg1: EnvPtr, arg2: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Block::Sub(arg1, arg2));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn tmul(arg1: EnvPtr, arg2: EnvPtr, store: &mut Store) -> TermPtr {
  store.push(Block::Mul(arg1, arg2));
  (store.len()-1) as TermPtr
}
#[inline(always)]
pub fn timp(store: &mut Store) -> TermPtr {
  store.push(Block::Impossible);
  (store.len()-1) as TermPtr
}

pub fn defs_to_store(defs: &Defs) -> (Store, Vec<TermPtr>) {
  let mut store = vec![];
  let mut map = vec![];
  for term in defs {
    // Assumes terms in defs are defined in order, which
    // means, in particular, that it can't have mutual
    // recursive definitions.
    // TODO: add support for unorded, mutual recursive
    // definitions
    map.push(store.len() as TermPtr);
    term_to_store(&mut store, &map, &term);
  }
  return (store, map)
}

pub fn term_to_store(store: &mut Store, map: &Vec<TermPtr>, term: &Term) -> TermPtr {
  match term {
    Term::Var(idx) => tvar(*idx, store),
    Term::Lam(bod) => {
      let lam_pos = store.len();
      let bod_pos = lam_pos+1;
      store.push(Block::Impossible);
      term_to_store(store, map, bod);
      store[lam_pos] = Block::Lam(bod_pos as TermPtr);
      lam_pos as TermPtr
    },
    Term::SLam(bod) => {
      let lam_pos = store.len();
      let bod_pos = lam_pos+1;
      store.push(Block::Impossible);
      term_to_store(store, map, bod);
      store[lam_pos] = Block::SLam(bod_pos as TermPtr);
      lam_pos as TermPtr
    },
    Term::App(fun, arg) => {
      let app_pos = store.len();
      let fun_pos = app_pos+1;
      store.push(Block::Impossible);
      term_to_store(store, map, fun);
      let arg_pos = term_to_store(store, map, arg);
      store[app_pos] = Block::App(fun_pos as TermPtr, arg_pos as TermPtr);
      app_pos as TermPtr
    },
    Term::Ref(idx) => tref(map[*idx as usize], store),
    Term::Int(num) => tint(*num, store),
    Term::Add(idx1, idx2) => tadd(*idx1, *idx2, store),
    Term::Mul(idx1, idx2) => tmul(*idx1, *idx2, store),
    Term::Sub(idx1, idx2) => tsub(*idx1, *idx2, store),
    Term::Eqz(idx, case1, case2) => {
      let eqz_pos = store.len();
      let case1_pos = eqz_pos+1;
      store.push(Block::Impossible);
      term_to_store(store, map, case1);
      let case2_pos = term_to_store(store, map, case2);
      store[eqz_pos] = Block::Eqz(*idx, case1_pos as TermPtr, case2_pos as TermPtr);
      eqz_pos as TermPtr
    },
  }
}
