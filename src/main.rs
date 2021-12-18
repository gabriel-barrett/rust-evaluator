use im::Vector;
use std::boxed::Box;

use evaluator::strict::*;
use evaluator::block::*;
use evaluator::term::*;

fn main() {
  macro_rules! lam {
    ($bod:expr) => {
      Term::Lam(Box::new($bod))
    };
  }

  macro_rules! app {
    ($fun:expr, $arg:expr) => {
      Term::App(Box::new($fun), Box::new($arg))
    };
  }

  macro_rules! eqz {
    ($idx:expr, $case1:expr, $case2:expr) => {
      Term::Eqz($idx, Box::new($case1), Box::new($case2))
    };
  }

  let add_t = lam!(lam!(Term::Add(1, 0)));
  let sub_t = lam!(lam!(Term::Sub(1, 0)));
  let cons_t = lam!(lam!(lam!(lam!(app!(app!(Term::Var(0), Term::Var(3)), Term::Var(2))))));
  let nil_t  = lam!(lam!(Term::Var(1)));
  let repeat_t = lam!(lam!(app!(lam!(eqz!(0, Term::Ref(3), app!(app!(Term::Ref(2), Term::Var(1)), app!(app!(Term::Ref(4), app!(app!(Term::Ref(1), Term::Var(2)), Term::Int(1))), Term::Var(1))))), Term::Var(1))));
  // let sum_t = lam!(app!(app!(Term::Var(0), Term::Int(0)), lam!(lam!(app!(app!(Term::Ref(0), Term::Var(1)), app!(Term::Ref(5), Term::Var(0)))))));
  let sum_t = lam!(lam!(app!(app!(Term::Var(1), Term::Var(0)), lam!(lam!(app!(app!(Term::Ref(5), Term::Var(0)), app!(app!(Term::Ref(0), Term::Var(1)), Term::Var(2))))))));
  let val_t = Term::Int(500000);
  let list_t = app!(app!(Term::Ref(4), Term::Ref(6)), Term::Int(1));
  // let main_t = app!(Term::Ref(5), Term::Ref(7));
  let main_t = app!(app!(Term::Ref(5), Term::Ref(7)), Term::Int(0));
  let defs = vec![add_t, sub_t, cons_t, nil_t, repeat_t, sum_t, val_t, list_t, main_t];

  let (store, defs) = defs_to_store(&defs);
  let env = Vector::new();
  let args = vec![];
  let mut heap = vec![];
  let val = eval(&store, &mut heap, defs[8], env, args);
  println!("{:?}", heap[val as usize]);
}
