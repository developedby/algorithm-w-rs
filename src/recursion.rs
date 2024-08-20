//! Simple implementation of Hindley-Milner type inference in Rust.
//! Extended with simply-recursive top-level function references.
//!
//! Implements Algorithm W, based on `https://github.com/mgrabmueller/AlgorithmW`.

use std::{
  collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
  str::FromStr,
};
use TSPL::{new_parser, Parser};

pub fn elaborate(program: Program) -> Result<ProgramTypes, String> {
  let types = infer_program(&program)?;
  let types = refresh_vars(types);
  Ok(types)
}

/* AST and other types */

#[derive(Default)]
pub struct Program {
  fns: BTreeMap<String, Term>,
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

impl Program {
  fn topological_order(&self) -> Result<Vec<String>, String> {
    let dep_graph = self.build_dependency_graph()?;
    let mut order = topological_sort(&dep_graph)?;
    order.reverse();
    Ok(order)
  }

  fn build_dependency_graph(&self) -> Result<HashMap<&str, HashSet<&str>>, String> {
    let mut dep_graph = HashMap::new();
    for (name, term) in &self.fns {
      let deps = self.find_dependencies(term);
      dep_graph.insert(name.as_str(), deps);
    }
    Ok(dep_graph)
  }

  fn find_dependencies<'a>(&'a self, term: &'a Term) -> HashSet<&'a str> {
    let mut deps = HashSet::new();
    let mut bound_vars = HashSet::new();
    self.find_dependencies_rec(term, &mut deps, &mut bound_vars);
    deps
  }

  fn find_dependencies_rec<'a>(
    &'a self,
    term: &'a Term,
    deps: &mut HashSet<&'a str>,
    bound_vars: &mut HashSet<&'a str>,
  ) {
    match term {
      Term::Var(name) => {
        if !bound_vars.contains(name.as_str()) && self.fns.contains_key(name) {
          deps.insert(name);
        }
      }
      Term::Lam(name, body) => {
        let is_new = bound_vars.insert(name);
        self.find_dependencies_rec(body, deps, bound_vars);
        if is_new {
          bound_vars.remove(name.as_str());
        }
      }
      Term::App(fun, arg) => {
        self.find_dependencies_rec(fun, deps, bound_vars);
        self.find_dependencies_rec(arg, deps, bound_vars);
      }
      Term::Let(name, val, body) => {
        self.find_dependencies_rec(val, deps, bound_vars);
        let is_new = bound_vars.insert(name);
        self.find_dependencies_rec(body, deps, bound_vars);
        if is_new {
          bound_vars.remove(name.as_str());
        }
      }
    }
  }
}

fn topological_sort(graph: &HashMap<&str, HashSet<&str>>) -> Result<Vec<String>, String> {
  let mut in_degree: HashMap<&str, usize> = graph.keys().map(|k| (*k, 0)).collect();
  for deps in graph.values() {
    for dep in deps {
      *in_degree.entry(dep).or_default() += 1;
    }
  }
  let mut queue: VecDeque<&str> =
    in_degree.iter().filter(|(_, &degree)| degree == 0).map(|(name, _)| *name).collect();
  let mut result = Vec::new();
  while let Some(node) = queue.pop_front() {
    result.push(node.to_string());
    if let Some(deps) = graph.get(node) {
      for dep in deps {
        if let Some(degree) = in_degree.get_mut(*dep) {
          *degree -= 1;
          if *degree == 0 {
            queue.push_back(dep);
          }
        }
      }
    }
  }
  if result.len() == graph.len() {
    Ok(result)
  } else {
    Err("Circular dependency detected".to_string())
  }
}

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

  /// Converts a monomorphic type into a type scheme by abstracting
  /// over the type variables free in `t`, but not free in the type
  /// environment.
  fn generalize(&self, env: &TypeEnv) -> Scheme {
    let vars_env = env.free_type_vars();
    let vars_t = self.free_type_vars();
    let vars = vars_t.difference(&vars_env).cloned().collect();
    Scheme(vars, self.clone())
  }
}

impl Scheme {
  fn free_type_vars(&self) -> BTreeSet<String> {
    let vars = self.1.free_type_vars();
    let bound_vars = self.0.iter().cloned().collect();
    vars.difference(&bound_vars).cloned().collect()
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
  /// Compose two substitutions.
  ///
  /// Applies the first substitution to the second, and then inserts the result into the first.
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

  fn append(&self, name: &str, scheme: Scheme) -> TypeEnv {
    let mut env = self.0.clone();
    env.insert(name.to_string(), scheme);
    TypeEnv(env)
  }
}

impl VarGen {
  fn fresh(&mut self) -> Type {
    let x = format!("a{}", self.0);
    self.0 += 1;
    Type::Var(x)
  }
}

fn infer_program(program: &Program) -> Result<ProgramTypes, String> {
  let mut types = BTreeMap::new();
  let mut var_gen = VarGen::default();
  let mut env = TypeEnv::default();

  // Get the topological order of functions
  let order = program.topological_order()?;
  eprintln!("Topological order: {order:?}");

  // Process functions in topological order
  for name in order {
    if let Some(body) = program.fns.get(&name) {
      let (s1, bod_t) = infer(&env, body, &mut var_gen)?;
      env = env.append(&name, bod_t.generalize(&env.subst(&s1)));
      types.insert(name, bod_t.subst(&s1));
    }
  }
  Ok(ProgramTypes(types))
}

/// Infer the type of a term in the given environment.
///
/// The type environment must contain bindings for all the free variables of the term.
///
/// The returned substitution records the type constraints imposed on type variables by the term.
/// The returned type is the type of the term.
fn infer(env: &TypeEnv, term: &Term, var_gen: &mut VarGen) -> Result<(Subst, Type), String> {
  maybe_grow(|| match term {
    Term::Var(name) => match env.0.get(name) {
      Some(scheme) => {
        let typ = scheme.instantiate(var_gen);
        Ok((Subst::default(), typ))
      }
      None => Err(format!("unbound variable '{}'", name)),
    },
    Term::Lam(name, body) => {
      let var_t = var_gen.fresh();
      let env = env.append(name, Scheme(vec![], var_t.clone()));
      let (s, bod_t) = infer(&env, body, var_gen)?;
      let var_t = var_t.subst(&s);
      Ok((s, Type::Arr(Box::new(var_t), Box::new(bod_t))))
    }
    Term::App(fun, arg) => {
      let (s1, fun_t) = infer(env, fun, var_gen)?;
      let (s2, arg_t) = infer(&env.subst(&s1), arg, var_gen)?;
      let app_t = var_gen.fresh();
      let s3 = unify(fun_t, Type::Arr(Box::new(arg_t), Box::new(app_t.clone())))?;
      Ok((s3.compose(&s2).compose(&s1), app_t.subst(&s3)))
    }
    Term::Let(name, val, body) => {
      let (s1, val_t) = infer(env, val, var_gen)?;
      let bod_env = env.append(name, val_t.generalize(&env.subst(&s1)));
      let (s2, bod_t) = infer(&bod_env, body, var_gen)?;
      Ok((s1.compose(&s2), bod_t))
    }
  })
}

fn unify(t1: Type, t2: Type) -> Result<Subst, String> {
  maybe_grow(|| match (t1, t2) {
    (Type::Arr(l1, r1), Type::Arr(l2, r2)) => {
      let s1 = unify(*l1, *l2)?;
      let s2 = unify(r1.subst(&s1), r2.subst(&s1))?;
      Ok(s2.compose(&s1))
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
  Ok(Subst(BTreeMap::from([(x.to_string(), t.clone())])))
}

fn refresh_vars(types: ProgramTypes) -> ProgramTypes {
  let mut new_types = BTreeMap::new();
  for (name, mut typ) in types.0 {
    refresh_vars_go(&mut typ, &mut BTreeMap::new(), &mut VarGen::default());
    new_types.insert(name, typ);
  }
  ProgramTypes(new_types)
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
      program.fns.insert(name, term);
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
    for (name, term) in &self.fns {
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
