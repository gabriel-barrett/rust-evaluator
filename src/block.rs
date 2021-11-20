use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum Block {
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
pub type Store = Vec<Block>;

#[inline(always)]
pub fn pvar(store: &mut Store, idx: EnvPtr) -> TermPtr {
  store.push(Block::Var(idx));
  store.len()-1
}
#[inline(always)]
pub fn plam(store: &mut Store, bod: TermPtr) -> TermPtr {
  store.push(Block::Lam(bod));
  store.len()-1
}
#[inline(always)]
pub fn papp(store: &mut Store, fun: TermPtr, arg: TermPtr) -> TermPtr {
  store.push(Block::App(fun, arg));
  store.len()-1
}
#[inline(always)]
pub fn pref(store: &mut Store, idx: TermPtr) -> TermPtr {
  store.push(Block::Ref(idx));
  store.len()-1
}
#[inline(always)]
pub fn popr(store: &mut Store, opr: Opr) -> TermPtr {
  store.push(Block::Opr(opr));
  store.len()-1
}
#[inline(always)]
pub fn pint(store: &mut Store, num: i64) -> TermPtr {
  store.push(Block::Int(num));
  store.len()-1
}
#[inline(always)]
pub fn pimpossible(store: &mut Store) -> TermPtr {
  store.push(Block::Impossible);
  store.len()-1
}

// pub fn build_store_from_defs<'a>(defs: &Defs) -> Store {
//   let mut store = vec![];
//   let mut ref_map = HashSet::new();
//   for i in 0..defs.len() {
//     if !ref_map.contains_key(i) {
//       // let (name, term_ir, typ_ir) = &defs[i];
//       // let term = ir_to_graph(term_ir, fun_defs);
//       // let typ_ = ir_to_graph(typ_ir, fun_defs);
//       // store.push(DefCell {
//       //   name: name.clone(),
//       //   term,
//       //   typ_,
//       // });
//       // if &*defs[i].0 == "main" {
//       //   main_idx = Some(i);
//       // }
//     }
//   }

//   store
// }

// pub fn from_term<'a>(store: &mut Store, term: &'a Term<'a>) -> TermPtr {
//   match term {
//     Term::Var(ptr) => {
//       store.push(Block::Var(*ptr));
//       store.len()-1
//     },
//     Term::Lam(bod) => {
//       let bod = from_term(store, bod);
//       store.push(Block::Lam(bod));
//       store.len()-1
//     },
//     Term::App(fun, arg) => {
//       let fun = from_term(store, fun);
//       let arg = from_term(store, arg);
//       store.push(Block::App(fun, arg));
//       store.len()-1
//     },
//     Term::Ref(_ptr) => {
//       // store.push(Block::Ref(*ptr));
//       // store.len()-1
//       todo!()
//     },
//     Term::Opr(opr) => {
//       store.push(Block::Opr(*opr));
//       store.len()-1
//     },
//     Term::Int(num) => {
//       store.push(Block::Int(*num));
//       store.len()-1
//     },
//   }
// }
