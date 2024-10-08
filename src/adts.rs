//! Hindley-Milner type system extended with ADTs.
//! Implements Algorithm W, based on `https://github.com/mgrabmueller/AlgorithmW`.

use std::{
  collections::{BTreeMap, BTreeSet},
  f32::consts::E,
  str::FromStr,
};
use TSPL::{new_parser, Parser};

pub fn elaborate(program: Program) -> Result<ProgramTypes, String> {
  let mut types = BTreeMap::new();
  let mut var_gen = VarGen::default();
  for (name, term) in &program.terms {
    let typ = infer_term(term, &mut var_gen)?;
    types.insert(name.clone(), typ);
  }
  let types = refresh_vars(ProgramTypes(types));
  Ok(types)
}

/* AST and other types */

#[derive(Default)]
pub struct Program {
  terms: BTreeMap<String, Term>,
  adts: BTreeMap<String, Adt>,

  // Maps constructor names to the name of the ADT they belong to.
  ctrs: BTreeMap<String, String>,
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
  Ref(String),
}

pub struct Adt {
  /// The arguments of the type constructor.
  args: Vec<String>,
  /// The constructors for a type, with the names of the fields and their types.
  ctrs: BTreeMap<String, Vec<(String, Type)>>,
}

/// A monomorphic Hindley-Milner type.
#[derive(Clone, Debug)]
pub enum Type {
  Var(String),
  Arr(Box<Type>, Box<Type>),
}

/// A type scheme, aka a polymorphic type.
#[derive(Clone)]
struct Scheme(Vec<String>, Type);

/// A finite mapping from type variables to types.
#[derive(Clone, Default, Debug)]
struct Subst(BTreeMap<String, Type>);

/// A mapping from term variables to type schemes.
#[derive(Clone, Default)]
struct TypeEnv(BTreeMap<String, Scheme>);

/// Variable generator for type variables.
#[derive(Default)]
struct VarGen(usize);

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

  /// Converts a type scheme into a monomorphic type by assigning
  /// fresh type variables to each variable bound by the scheme.
  fn instantiate(&self, var_gen: &mut VarGen) -> Type {
    let new_vars = self.0.iter().map(|_| var_gen.fresh());
    let subst = Subst(self.0.iter().cloned().zip(new_vars).collect());
    self.1.subst(&subst)
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

impl VarGen {
  fn fresh(&mut self) -> Type {
    let x = format!("a{}", self.0);
    self.0 += 1;
    Type::Var(x)
  }
}

/// Infer the type of a term in the given environment.
fn infer_term(term: &Term, program: &Program, var_gen: &mut VarGen) -> Result<Type, String> {
  let (subst, typ) = infer_term_go(&TypeEnv::default(), term, program, var_gen)?;
  Ok(typ.subst(&subst))
}

/// Infer the type of a term in the given environment.
///
/// The type environment must contain bindings for all the free variables of the term.
///
/// The returned substitution records the type constraints imposed on type variables by the term.
/// The returned type is the type of the term.
fn infer_term_go(
  env: &TypeEnv,
  term: &Term,
  program: &Program,
  var_gen: &mut VarGen,
) -> Result<(Subst, Type), String> {
  maybe_grow(|| match term {
    Term::Var(name) => match env.0.get(name) {
      Some(scheme) => {
        let typ = scheme.instantiate(var_gen);
        Ok((Subst::default(), typ))
      }
      None => Err(format!("unbound variable '{}'", name)),
    },
    Term::Lam(name, body) => {
      let type_var = var_gen.fresh();
      let mut env = env.clone();
      env.0.insert(name.clone(), Scheme(vec![], type_var.clone()));
      let (subst, bod_type) = infer_term_go(&env, body, program, var_gen)?;
      let arg_type = type_var.subst(&subst);
      let lam_type = Type::Arr(Box::new(arg_type), Box::new(bod_type));
      Ok((subst, lam_type))
    }
    Term::App(fun, arg) => {
      let type_var = var_gen.fresh();
      let (subst1, fun_type) = infer_term_go(env, fun, program, var_gen)?;
      let (subst2, arg_type) = infer_term_go(&env.subst(&subst1), arg, program, var_gen)?;
      let subst3 = unify(fun_type, Type::Arr(Box::new(arg_type), Box::new(type_var.clone())))?;
      let subst = subst3.compose(&subst2).compose(&subst1);
      let app_type = type_var.subst(&subst);
      Ok((subst, app_type))
    }
    Term::Let(name, val, body) => {
      let (subst1, val_type) = infer_term_go(env, val, program, var_gen)?;
      let val_env = env.subst(&subst1);
      let val_scheme = val_env.generalize(&val_type);
      let mut body_env = env.clone();
      body_env.0.insert(name.clone(), val_scheme);
      let (subst2, body_type) = infer_term_go(&body_env, body, program, var_gen)?;
      Ok((subst1.compose(&subst2), body_type))
    }
    Term::Ref(name) => {
      if let Some(ctr) = program.ctrs.get(name) {
        let adt = program.adts.get(ctr).unwrap();
        let fields = adt.ctrs.get(name).unwrap();
        // field1 -> ... -> fieldN -> (ctr_name a1 ... aN)
        todo!()
      } else {
        Err(format!("unbound constructor '{}'", name))
      }
    }
  })
}

fn unify(t1: Type, t2: Type) -> Result<Subst, String> {
  maybe_grow(|| match (t1, t2) {
    (Type::Arr(t11, t12), Type::Arr(t21, t22)) => {
      let s1 = unify(*t11, *t21)?;
      let s2 = unify(t12.subst(&s1), t22.subst(&s1))?;
      Ok(s1.compose(&s2))
    }
    (t1, Type::Var(x)) => bind_var(x, t1),
    (Type::Var(x), t2) => bind_var(x, t2),
  })
}

/// Try to bind variable `x` to `t` and return that binding as a substitution.
///
/// Doesn't bind a variable to itself and doesn't bind a variable if it occurs free in `t`.
fn bind_var(x: String, t: Type) -> Result<Subst, String> {
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

fn refresh_vars(mut types: ProgramTypes) -> ProgramTypes {
  for typ in types.0.values_mut() {
    refresh_vars_go(typ, &mut BTreeMap::new(), &mut VarGen::default());
  }
  types
}

fn refresh_vars_go(typ: &mut Type, map: &mut BTreeMap<String, Type>, var_gen: &mut VarGen) {
  maybe_grow(|| match typ {
    Type::Var(x) => {
      if let Some(y) = map.get(x) {
        *typ = y.clone();
      } else {
        let y = var_gen.fresh();
        map.insert(x.clone(), y.clone());
        *typ = y;
      }
    }
    Type::Arr(t1, t2) => {
      refresh_vars_go(t1, map, var_gen);
      refresh_vars_go(t2, map, var_gen);
    }
  })
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
