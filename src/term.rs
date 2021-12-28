use std::boxed::Box;

#[derive(Debug, Clone)]
pub enum Term {
  // Lambda calculus constructs
  Var(EnvPtr),
  Lam(Box<Term>),
  SLam(Box<Term>),
  App(Box<Term>, Box<Term>),
  // Reference to global definitions
  Ref(DefPtr),
  // Integers and operations on integers.
  // Notice how operations like `Add` take EnvPtr instead of
  // Box<Term>. This is means that when evaluating, it will
  // take the value from the environment, which is already a
  // value (when the arguments are strict). Primitive operations
  // should, therefore, be wrapped in Lam nodes.
  // TODO: For lazy evaluation, I'll probably add a new, strict
  // Lam to be used for primitive values
  Int(i64),
  Add(EnvPtr, EnvPtr),
  Mul(EnvPtr, EnvPtr),
  Sub(EnvPtr, EnvPtr),
  Eqz(EnvPtr, Box<Term>, Box<Term>),
}

pub type EnvPtr = u32;
pub type DefPtr = u32;

pub type Defs = Vec<Term>;
