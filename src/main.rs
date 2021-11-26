use evaluator::semi_strict::*;
use evaluator::term::*;

fn main() {
  let mut store = vec![];
  // Macro to help building terms manually
  macro_rules! var {
    ($idx:expr) => {
      tvar($idx, &mut store)
    };
  }
  macro_rules! lam {
    ($bod:expr) => {
      tlam($bod, &mut store)
    };
  }
  macro_rules! app {
    ($fun:expr, $arg:expr) => {
      tapp($fun, $arg, &mut store)
    };
  }
  macro_rules! refr {
    ($idx:expr) => {
      tref($idx, &mut store)
    };
  }
  macro_rules! int {
    ($num:expr) => {
      tint($num, &mut store)
    };
  }
  macro_rules! add {
    ($arg1:expr, $arg2:expr) => {
      tadd($arg1, $arg2, &mut store)
    };
  }
  macro_rules! sub {
    ($arg1:expr, $arg2:expr) => {
      tsub($arg1, $arg2, &mut store)
    };
  }
  macro_rules! eqz {
    ($arg1:expr, $arg2:expr, $arg3:expr) => {
      teqz($arg1, $arg2, $arg3, &mut store)
    };
  }

  let add = lam!(lam!(add!(1, 0)));
  let sub = lam!(lam!(sub!(1, 0)));
  let cons_t = lam!(lam!(lam!(lam!(app!(app!(var!(0), var!(3)), app!(app!(var!(2), var!(1)), var!(0)))))));
  let nil_t  = lam!(lam!(var!(1)));

  // repeat is recursive, so the recursive call will be replaced with impossible until we know the index of repeat
  let repeat_t =
    lam!(lam!(
      app!(
        lam!(eqz!(0,
                  refr!(nil_t),
                  app!(app!(refr!(cons_t), var!(1)), app!(app!(timp(&mut store), app!(app!(refr!(sub), var!(2)), int!(1))), var!(1))))),
        var!(1))));
  for i in 0..store.len() {
    match store[i] {
      Term::Impossible => (),
      _ => continue,
    };
    store[i] = Term::Ref(repeat_t)
  }

  // \xs -> xs 0 (\x rec -> add x rec)
  let sum_t = lam!(app!(app!(var!(0), int!(0)), lam!(lam!(app!(app!(refr!(add), var!(1)), var!(0))))));
  let val_t = int!(500000);
  let list_t = app!(app!(refr!(repeat_t), refr!(val_t)), int!(1));
  let main_t = app!(refr!(sum_t), refr!(list_t));

  let mut heap = vec![];
  let val = eval(&store, &mut heap, main_t);
  println!("{:?}", heap[val as usize]);
}
