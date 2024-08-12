//! Simple implementation of Hindley-Milner type inference in Rust.
//! Implements Algorithm W, based on `https://github.com/mgrabmueller/AlgorithmW`.

use std::{collections::{BTreeMap, BTreeSet}, str::FromStr};
use TSPL::{new_parser, Parser};

pub fn infer(program: Program) -> Result<ProgramTypes, String> {
  let mut ctx = InferCtx::default();
  ctx.infer_program(program)
}

/* AST */

#[derive(Default)]
pub struct Program {
  terms: BTreeMap<String, Term>,
}

#[derive(Default)]
pub struct ProgramTypes(BTreeMap<String, Type>);

/// A term in our system of lambda calculus with some extensions.
#[derive(Clone)]
pub enum Term {
  Var(String),
  Lam(String, Box<Term>),
  App(Box<Term>, Box<Term>),
  Let(String, Box<Term>, Box<Term>),
}

/// A monomorphic Hindley-Milner type.
#[derive(Clone, Debug)]
pub enum Type {
  Var(String),
  Arr(Box<Type>, Box<Type>),
}

/* Types */

/// A type scheme, aka a polymorphic type.
#[derive(Clone)]
struct Scheme(Vec<String>, Type);

/// A finite mapping from type variables to types.
#[derive(Clone, Default, Debug)]
struct Subst(BTreeMap<String, Type>);

/// A mapping from term variables to type schemes.
#[derive(Clone, Default)]
struct TypeEnv(BTreeMap<String, Scheme>);

/// State monad for type inference.
///
/// Used to generate fresh type variables needed for type inference.
#[derive(Default)]
struct InferCtx {
  var_counter: usize,
}

/* Implementations */

impl Type {
  fn free_type_vars(&self) -> BTreeSet<String> {
    maybe_grow(|| match self {
      Type::Var(x) => BTreeSet::from([x.clone()]),
      Type::Arr(t1, t2) => t1.free_type_vars().union(&t2.free_type_vars()).cloned().collect(),
    })
  }

  fn subst(&self, subst: &Subst) -> Type {
    maybe_grow(|| match self {
      Type::Var(nam) => match subst.0.get(nam) {
        Some(new) => new.clone(),
        None => self.clone(),
      },
      Type::Arr(t1, t2) => Type::Arr(Box::new(t1.subst(subst)), Box::new(t2.subst(subst))),
    })
  }
}

impl Scheme {
  fn free_type_vars(&self) -> BTreeSet<String> {
    let vars = self.1.free_type_vars();
    let bound_vars = self.0.iter().cloned().collect();
    let free_vars = vars.difference(&bound_vars);
    free_vars.cloned().collect()
  }

  fn subst(&self, subst: &Subst) -> Scheme {
    let mut subst = subst.clone();
    for x in self.0.iter() {
      subst.0.remove(x);
    }
    let t = self.1.subst(&subst);
    Scheme(self.0.clone(), t)
  }
}

impl Subst {
  fn compose(&self, other: &Subst) -> Subst {
    let other = other.0.iter().map(|(x, t)| (x.clone(), t.subst(self)));
    let subst = self.0.iter().map(|(x, t)| (x.clone(), t.clone())).chain(other).collect();
    Subst(subst)
  }
}

impl TypeEnv {
  fn free_type_vars(&self) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for scheme in self.0.values() {
      let scheme_vars = scheme.free_type_vars();
      vars = vars.union(&scheme_vars).cloned().collect();
    }
    vars
  }

  fn subst(&self, subst: &Subst) -> TypeEnv {
    let env = self.0.iter().map(|(x, scheme)| (x.clone(), scheme.subst(subst))).collect();
    TypeEnv(env)
  }

  /// Converts a monomorphic type into a type scheme by abstracting
  /// over the type variables free in `t`, but not free in the type
  /// environment.
  fn generalize(&self, t: &Type) -> Scheme {
    let vars_env = self.free_type_vars();
    let vars_t = t.free_type_vars();
    let vars = vars_t.difference(&vars_env).cloned().collect();
    Scheme(vars, t.clone())
  }
}

impl InferCtx {
  fn infer_program(&mut self, program: Program) -> Result<ProgramTypes, String> {
    let mut types = BTreeMap::new();
    for (name, term) in &program.terms {
      let typ = self.infer(term)?;
      types.insert(name.clone(), typ);
    }
    let types = self.refresh_vars(ProgramTypes(types));
    Ok(types)
  }

  /// Infer the type of a term in the given environment.
  fn infer(&mut self, term: &Term) -> Result<Type, String> {
    let (subst, typ) = self.infer_term(&TypeEnv::default(), term)?;
    Ok(typ.subst(&subst))
  }

  /// Infer the type of a term in the given environment.
  ///
  /// The type environment must contain bindings for all the free variables of the term.
  ///
  /// The returned substitution records the type constraints imposed on type variables by the term.
  /// The returned type is the type of the term.
  fn infer_term(&mut self, env: &TypeEnv, term: &Term) -> Result<(Subst, Type), String> {
    maybe_grow(|| match term {
      Term::Var(name) => match env.0.get(name) {
        Some(scheme) => {
          let typ = self.instantiate(scheme);
          Ok((Subst::default(), typ))
        }
        None => Err(format!("unbound variable '{}'", name)),
      },
      Term::Lam(name, body) => {
        let type_var = self.new_type_var();
        let mut env = env.clone();
        env.0.insert(name.clone(), Scheme(vec![], type_var.clone()));
        let (subst, bod_type) = self.infer_term(&env, body)?;
        let arg_type = type_var.subst(&subst);
        let lam_type = Type::Arr(Box::new(arg_type), Box::new(bod_type));
        Ok((subst, lam_type))
      }
      Term::App(fun, arg) => {
        let type_var = self.new_type_var();
        let (subst1, fun_type) = self.infer_term(env, fun)?;
        let (subst2, arg_type) = self.infer_term(&env.subst(&subst1), arg)?;
        let subst3 =
          self.unify(fun_type, Type::Arr(Box::new(arg_type), Box::new(type_var.clone())))?;
        let subst = subst3.compose(&subst2).compose(&subst1);
        let app_type = type_var.subst(&subst);
        Ok((subst, app_type))
      }
      Term::Let(name, val, body) => {
        let (subst1, val_type) = self.infer_term(env, val)?;
        let val_env = env.subst(&subst1);
        let val_scheme = val_env.generalize(&val_type);
        let mut body_env = env.clone();
        body_env.0.insert(name.clone(), val_scheme);
        let (subst2, body_type) = self.infer_term(&body_env, body)?;
        Ok((subst1.compose(&subst2), body_type))
      }
    })
  }

  /// Converts a type scheme into a monomorphic type by assigning
  /// fresh type variables to each variable bound by the scheme.
  fn instantiate(&mut self, scheme: &Scheme) -> Type {
    let new_vars = scheme.0.iter().map(|_| self.new_type_var());
    let subst = Subst(scheme.0.iter().cloned().zip(new_vars).collect());
    scheme.1.subst(&subst)
  }

  fn unify(&mut self, t1: Type, t2: Type) -> Result<Subst, String> {
    maybe_grow(|| match (t1, t2) {
      (Type::Arr(t11, t12), Type::Arr(t21, t22)) => {
        let s1 = self.unify(*t11, *t21)?;
        let s2 = self.unify(t12.subst(&s1), t22.subst(&s1))?;
        Ok(s1.compose(&s2))
      }
      (t1, Type::Var(x)) => self.bind_var(x, t1),
      (Type::Var(x), t2) => self.bind_var(x, t2),
    })
  }

  /// Try to bind variable `x` to `t` and return that binding as a substitution.
  ///
  /// Doesn't bind a variable to itself and doesn't bind a variable if it occurs free in `t`.
  fn bind_var(&mut self, x: String, t: Type) -> Result<Subst, String> {
    if let Type::Var(y) = &t {
      if y == &x {
        return Ok(Subst::default());
      }
    }
    if t.free_type_vars().contains(&x) {
      return Err(format!(
        "cannot bind variable '{x}' to term {t} because it occurs as a free variable"
      ));
    }
    Ok(Subst(BTreeMap::from([(x, t)])))
  }

  fn new_type_var(&mut self) -> Type {
    let x = format!("a{}", self.var_counter);
    self.var_counter += 1;
    Type::Var(x)
  }

  fn refresh_vars(&mut self, mut types: ProgramTypes) -> ProgramTypes {
    for typ in types.0.values_mut() {
      self.var_counter = 0;
      self.refresh_vars_in_type(typ, &mut BTreeMap::new());
    }
    types
  }

  fn refresh_vars_in_type(&mut self, typ: &mut Type, map: &mut BTreeMap<String, String>) {
    maybe_grow(|| match typ {
      Type::Var(x) => {
        if let Some(y) = map.get(x) {
          *typ = Type::Var(y.clone());
        } else {
          let y = format!("a{}", self.var_counter);
          self.var_counter += 1;
          map.insert(x.clone(), y.clone());
          *typ = Type::Var(y);
        }
      }
      Type::Arr(t1, t2) => {
        self.refresh_vars_in_type(t1, map);
        self.refresh_vars_in_type(t2, map);
      }
    })
  }
}

/* Parser */

new_parser!(TermParser);

impl TermParser<'_> {
  fn parse_program(&mut self) -> Result<Program, String> {
    let mut program = Program::default();
    self.skip_trivia();
    while !self.is_eof() {
      let name = self.parse_name()?;
      self.consume("=")?;
      let term = self.parse_term()?;
      program.terms.insert(name, term);
      self.skip_trivia();
    }
    Ok(program)
  }

  fn parse_term(&mut self) -> Result<Term, String> {
    maybe_grow(|| {
      self.skip_trivia();
      if self.starts_with("λ") || self.starts_with("@") {
        // Lambda
        self.advance_one();
        let name = self.parse_name()?;
        let body = self.parse_term()?;
        Ok(Term::Lam(name, Box::new(body)))
      } else if self.starts_with("let") {
        // Let
        self.advance_many(3);
        let name = self.parse_name()?;
        self.consume("=")?;
        let val = self.parse_term()?;
        self.consume(";")?;
        let body = self.parse_term()?;
        Ok(Term::Let(name, Box::new(val), Box::new(body)))
      } else if self.starts_with("(") {
        // Application
        self.advance_one();
        let head = self.parse_term()?;
        let mut args = Vec::new();
        self.skip_trivia();
        while !self.starts_with(")") {
          args.push(self.parse_term()?);
          self.skip_trivia();
        }
        self.consume(")")?;
        let term = args.into_iter().fold(head, |acc, arg| Term::App(Box::new(acc), Box::new(arg)));
        Ok(term)
      } else {
        // Variable
        let name = self.parse_name()?;
        Ok(Term::Var(name))
      }
    })
  }
}

impl FromStr for Term {
  type Err = String;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    TermParser::new(s).parse_term()
  }
}

impl FromStr for Program {
  type Err = String;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    TermParser::new(s).parse_program()
  }
}

/* Display */

impl std::fmt::Display for Program {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (name, term) in &self.terms {
      writeln!(f, "{} = {}", name, term)?;
    }
    Ok(())
  }
}

impl std::fmt::Display for ProgramTypes {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (name, typ) in &self.0 {
      writeln!(f, "{} : {}", name, typ)?;
    }
    Ok(())
  }
}

impl std::fmt::Display for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    maybe_grow(|| match self {
      Term::Var(name) => write!(f, "{}", name),
      Term::Lam(name, body) => write!(f, "λ {} {}", name, body),
      Term::App(fun, arg) => write!(f, "({} {})", fun, arg),
      Term::Let(name, val, body) => write!(f, "(let {} = {}; {})", name, val, body),
    })
  }
}

impl std::fmt::Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    maybe_grow(|| match self {
      Type::Var(name) => write!(f, "{}", name),
      Type::Arr(t1, t2) => write!(f, "({} -> {})", t1, t2),
    })
  }
}

impl std::fmt::Display for Scheme {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for x in &self.0 {
      write!(f, "∀{} ", x)?;
    }
    write!(f, "{}", self.1)
  }
}

/* Utils */

fn maybe_grow<R, F>(f: F) -> R
where
  F: FnOnce() -> R,
{
  stacker::maybe_grow(1024 * 32, 1024 * 1024, f)
}
