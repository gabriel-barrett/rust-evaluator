use im::Vector;

// use evaluator::lazy;
use evaluator::semi_strict;
use evaluator::term::*;

fn main() {
  let mut store = vec![];
  // Macro to help building terms manually
  macro_rules! var {
    ($idx:expr) => {
      pvar($idx, &mut store)
    };
  }
  macro_rules! lam {
    ($bod:expr) => {
      plam($bod, &mut store)
    };
  }
  macro_rules! app {
    ($fun:expr, $arg:expr) => {
      papp($fun, $arg, &mut store)
    };
  }
  macro_rules! refr {
    ($idx:expr) => {
      pref($idx, &mut store)
    };
  }
  macro_rules! opr {
    ($opr:expr) => {
      popr($opr, &mut store)
    };
  }
  macro_rules! int {
    ($num:expr) => {
      pint($num, &mut store)
    };
  }

  let cons_t = lam!(lam!(lam!(lam!(app!(app!(var!(0), var!(3)), app!(app!(var!(2), var!(1)), var!(0)))))));
  let nil_t  = lam!(lam!(var!(1)));

  // repeat is recursive, so the recursive call will be replaced with impossible until we know the index of repeat
  let repeat_t = lam!(lam!(app!(app!(app!(opr!(Opr::Eqz), var!(1)), refr!(nil_t)), app!(app!(refr!(cons_t), var!(0)), app!(app!(pimpossible(&mut store), app!(app!(opr!(Opr::Sub), var!(1)), int!(1))), var!(0))))));
  for i in 0..store.len() {
    match store[i] {
      Term::Impossible => (),
      _ => continue,
    };
    store[i] = Term::Ref(repeat_t)
  }

  let sum_t = lam!(app!(app!(var!(0), int!(0)), lam!(lam!(app!(app!(opr!(Opr::Add), var!(1)), var!(0))))));
  let val_t = int!(50000);
  let list_t = app!(app!(refr!(repeat_t), refr!(val_t)), int!(1));
  let main_t = app!(refr!(sum_t), refr!(list_t));

  // let env = Vector::new();
  // let args = vec![];
  // lazy::print_int(lazy::eval(&defs, defs[6], env, args));

  let env = Vector::new();
  let args = vec![];
  semi_strict::print_int(semi_strict::eval(&store, main_t, env, args));
}
