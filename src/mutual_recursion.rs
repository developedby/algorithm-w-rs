//! Hindley-Milner type system extended with mutual recursion.
//! Implements Algorithm W, based on `https://github.com/mgrabmueller/AlgorithmW`.

use std::{
  collections::{BTreeMap, BTreeSet},
  str::FromStr,
};
use TSPL::{new_parser, Parser};

pub fn elaborate(mut program: Program) -> Result<ProgramTypes, String> {
  program.resolve_refs()?;
  let rec_groups = DefComponents::from_program(&program);
  let types = infer_program(&program, &rec_groups)?;
  let types = refresh_vars(types);
  Ok(types)
}

/* AST */

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
  Ref(String),
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

/// Variable generator for type variables.
#[derive(Default)]
struct VarGen(usize);

/// A store of the strongly connected components formed by the
/// dependency graph of the program's functions.
struct DefComponents(Vec<BTreeSet<String>>);

/* Implementations */

impl Term {
  fn resolve_refs(&mut self, program: &Program) -> Result<(), String> {
    self.resolve_refs_go(program, &mut HashSet::new())
  }

  fn resolve_refs_go(
    &mut self,
    program: &Program,
    scope: &mut HashSet<String>,
  ) -> Result<(), String> {
    maybe_grow(|| {
      match self {
        Term::Var(name) => {
          if !scope.contains(name) {
            if program.fns.contains_key(name) {
              *self = Term::Ref(name.clone());
            } else {
              return Err(format!("unbound variable '{}'", name));
            }
          }
        }
        Term::Lam(name, body) => {
          let new_nam = scope.insert(name.clone());
          body.resolve_refs_go(program, scope)?;
          if new_nam {
            scope.remove(name);
          }
        }
        Term::App(fun, arg) => {
          fun.resolve_refs_go(program, scope)?;
          arg.resolve_refs_go(program, scope)?;
        }
        Term::Let(_, val, body) => {
          val.resolve_refs_go(program, scope)?;
          body.resolve_refs_go(program, scope)?;
        }
        Term::Ref(_) => unreachable!(),
      }
      Ok(())
    })
  }
}

impl Program {
  fn resolve_refs(&mut self) -> Result<(), String> {
    let names = self.fns.keys().cloned().collect::<Vec<_>>();
    for name in names {
      let mut body = std::mem::replace(self.fns.get_mut(&name).unwrap(), Term::Ref(String::new()));
      body.resolve_refs(self)?;
      *self.fns.get_mut(&name).unwrap() = body;
    }
    Ok(())
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
    let new_vars = self.0.iter().map(|_| var_gen.fresh_var());
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
}

impl VarGen {
  fn fresh_name(&mut self) -> String {
    let x = format!("a{}", self.0);
    self.0 += 1;
    x
  }

  fn fresh_var(&mut self) -> Type {
    Type::Var(self.fresh_name())
  }
}

fn infer_program(program: &Program, rec_groups: &DefComponents) -> Result<ProgramTypes, String> {
  let mut types = BTreeMap::new();
  let mut var_gen = VarGen::default();
  let mut env = TypeEnv::default();
  for group in &rec_groups.0 {
    // Start assuming a fresh type variable for each function in the group.
    let mut fresh_vars = Vec::new();
    for name in group {
      let var_name = var_gen.fresh_name();
      fresh_vars.push(var_name.clone());
      env.0.insert(name.clone(), Scheme(vec![], Type::Var(var_name)));
    }

    // Infer the types of the functions in the group.
    for (var, name) in fresh_vars.into_iter().zip(group.iter()) {
      let (subst, typ) = infer_term(&env, &program.fns[name], &mut var_gen)?;
      let typ = if let Some(assumed_type) = subst.0.get(&var) {
        // If a recursive function, we unify the assumed type with the inferred type.
        let subst2 = unify(&typ, assumed_type)?;
        let subst = subst2.compose(&subst);
        env = env.subst(&subst);
        subst.0[&var].clone()
      } else {
        // Otherwise, the inferred type is already the type.
        typ
      };
      types.insert(name.clone(), typ);
    }

    // Generalize the types of the functions in the group so that
    // they are polymorphic when called elsewhere.
    for name in group {
      let typ = types.get_mut(name).unwrap();
      let scheme = typ.generalize(&TypeEnv::default());
      env.0.insert(name.clone(), scheme);
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
fn infer_term(env: &TypeEnv, term: &Term, var_gen: &mut VarGen) -> Result<(Subst, Type), String> {
  maybe_grow(|| {
    match term {
      Term::Var(name) => match env.0.get(name) {
        Some(scheme) => {
          let typ = scheme.instantiate(var_gen);
          Ok((Subst::default(), typ))
        }
        None => Err(format!("unbound variable '{}'", name)),
      },
      Term::Lam(name, body) => {
        let type_var = var_gen.fresh_var();
        let mut env = env.clone();
        env.0.insert(name.clone(), Scheme(vec![], type_var.clone()));
        let (subst, bod_type) = infer_term(&env, body, var_gen)?;
        let arg_type = type_var.subst(&subst);
        let lam_type = Type::Arr(Box::new(arg_type), Box::new(bod_type));
        Ok((subst, lam_type))
      }
      Term::App(fun, arg) => {
        let type_var = var_gen.fresh_var();
        let (subst1, fun_type) = infer_term(env, fun, var_gen)?;
        let (subst2, arg_type) = infer_term(&env.subst(&subst1), arg, var_gen)?;
        let subst3 = unify(&fun_type, &Type::Arr(Box::new(arg_type), Box::new(type_var.clone())))?;
        let subst = subst3.compose(&subst2).compose(&subst1);
        let app_type = type_var.subst(&subst);
        Ok((subst, app_type))
      }
      Term::Let(name, val, body) => {
        let (subst1, val_type) = infer_term(env, val, var_gen)?;
        let val_env = env.subst(&subst1);
        let val_scheme = val_type.generalize(&val_env);
        let mut body_env = env.clone();
        body_env.0.insert(name.clone(), val_scheme);
        let (subst2, body_type) = infer_term(&body_env, body, var_gen)?;
        Ok((subst1.compose(&subst2), body_type))
      }
      Term::Ref(name) => {
        // All references will be in the environment since we check them in topological order.
        let scheme = env.0.get(name).unwrap();
        let typ = scheme.instantiate(var_gen);
        Ok((Subst::default(), typ))
      }
    }
  })
}

fn unify(t1: &Type, t2: &Type) -> Result<Subst, String> {
  maybe_grow(|| match (t1, t2) {
    (Type::Arr(t11, t12), Type::Arr(t21, t22)) => {
      let s1 = unify(t11, t21)?;
      let s2 = unify(&t12.subst(&s1), &t22.subst(&s1))?;
      Ok(s1.compose(&s2))
    }
    (t1, Type::Var(x)) => bind_var(x, t1),
    (Type::Var(x), t2) => bind_var(x, t2),
  })
}

/// Try to bind variable `x` to `t` and return that binding as a substitution.
///
/// Doesn't bind a variable to itself and doesn't bind a variable if it occurs free in `t`.
fn bind_var(x: &str, t: &Type) -> Result<Subst, String> {
  if let Type::Var(y) = t {
    if y == x {
      return Ok(Subst::default());
    }
  }
  if t.free_type_vars().contains(x) {
    return Err(format!(
      "cannot bind variable '{x}' to term {t} because it occurs as a free variable"
    ));
  }
  Ok(Subst(BTreeMap::from([(x.to_string(), t.clone())])))
}

use std::collections::{HashMap, HashSet};

impl DefComponents {
  fn from_program(program: &Program) -> DefComponents {
    type DependencyGraph<'a> = HashMap<&'a str, HashSet<&'a str>>;

    fn collect_dependencies<'a>(term: &'a Term, def_name: &'a str, deps: &mut HashSet<&'a str>) {
      match term {
        Term::Var(_) => {}
        Term::Lam(_, body) => collect_dependencies(body, def_name, deps),
        Term::App(fun, arg) => {
          collect_dependencies(fun, def_name, deps);
          collect_dependencies(arg, def_name, deps);
        }
        Term::Let(_, val, body) => {
          collect_dependencies(val, def_name, deps);
          collect_dependencies(body, def_name, deps);
        }
        Term::Ref(name) => {
          if name != def_name {
            deps.insert(name);
          }
        }
      }
    }

    fn strong_connect<'a>(
      v: &'a str,
      deps: &DependencyGraph<'a>,
      index: &mut usize,
      index_map: &mut HashMap<&'a str, usize>,
      low_link: &mut HashMap<&'a str, usize>,
      stack: &mut Vec<&'a str>,
      components: &mut Vec<BTreeSet<String>>,
    ) {
      maybe_grow(|| {
        index_map.insert(v, *index);
        low_link.insert(v, *index);
        *index += 1;
        stack.push(v);

        if let Some(neighbors) = deps.get(v) {
          for w in neighbors {
            if !index_map.contains_key(w) {
              // Successor w has not yet been visited, recurse on it.
              strong_connect(w, deps, index, index_map, low_link, stack, components);
              low_link.insert(v, low_link[v].min(low_link[w]));
            } else if stack.contains(w) {
              // Successor w is in stack S and hence in the current SCC.
              low_link.insert(v, low_link[v].min(index_map[w]));
            } else {
              // If w is not on stack, then (v, w) is an edge pointing
              // to an SCC already found and must be ignored.
            }
          }
        }

        // If v is a root node, pop the stack and generate an SCC.
        if low_link[v] == index_map[v] {
          let mut component = BTreeSet::new();
          while let Some(w) = stack.pop() {
            component.insert(w.to_string());
            if w == v {
              break;
            }
          }
          components.push(component);
        }
      })
    }

    // Build the dependency graph
    let mut deps = DependencyGraph::default();
    for (name, body) in &program.fns {
      let mut fn_deps = Default::default();
      collect_dependencies(body, name, &mut fn_deps);
      deps.insert(name, fn_deps);
    }

    // Run Tarjan's algorithm
    let mut index = 0;
    let mut stack = Vec::new();
    let mut index_map = HashMap::new();
    let mut low_link = HashMap::new();
    let mut components = Vec::new();
    for name in deps.keys() {
      if !index_map.contains_key(name) {
        strong_connect(
          name,
          &deps,
          &mut index,
          &mut index_map,
          &mut low_link,
          &mut stack,
          &mut components,
        );
      }
    }
    DefComponents(components)
  }
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
        let y = var_gen.fresh_var();
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
      Term::Lam(name, body) => write!(f, "λ{} {}", name, body),
      Term::App(fun, arg) => write!(f, "({} {})", fun, arg),
      Term::Let(name, val, body) => write!(f, "(let {} = {}; {})", name, val, body),
      Term::Ref(name) => write!(f, "!{}", name),
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
