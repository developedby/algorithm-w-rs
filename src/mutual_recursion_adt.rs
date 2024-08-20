//! Hindley-Milner type system extended with recursive ADTs and mutual recursion.
//!
//! Implements Algorithm W, based on `https://github.com/mgrabmueller/AlgorithmW`.

use std::{
  collections::{BTreeMap, BTreeSet, HashMap, HashSet},
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
  funs: BTreeMap<String, Term>,
  adts: BTreeMap<String, Adt>,
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
  Mat(String, Box<Term>, Vec<(String, Term)>),
}

/// A monomorphic Hindley-Milner type.
#[derive(Clone, Debug)]
pub enum Type {
  Var(String),
  Arr(Box<Type>, Box<Type>),
  Ctr(String, Vec<Type>),
}

pub struct Adt {
  name: String,
  vars: Vec<String>,
  ctrs: Vec<Ctr>,
}

pub struct Ctr {
  name: String,
  fields: Vec<(String, Type)>,
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

struct RecGroups(Vec<Vec<String>>);

/* Implementations */

impl Type {
  fn free_type_vars(&self) -> BTreeSet<String> {
    maybe_grow(|| match self {
      Type::Var(x) => BTreeSet::from([x.clone()]),
      Type::Arr(t1, t2) => t1.free_type_vars().union(&t2.free_type_vars()).cloned().collect(),
      Type::Ctr(_, ts) => ts.iter().flat_map(|t| t.free_type_vars()).collect(),
    })
  }

  fn subst(&self, subst: &Subst) -> Type {
    maybe_grow(|| match self {
      Type::Var(nam) => match subst.0.get(nam) {
        Some(new) => new.clone(),
        None => self.clone(),
      },
      Type::Arr(t1, t2) => Type::Arr(Box::new(t1.subst(subst)), Box::new(t2.subst(subst))),
      Type::Ctr(name, ts) => Type::Ctr(name.clone(), ts.iter().map(|t| t.subst(subst)).collect()),
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

impl RecGroups {
  fn from_program(program: &Program) -> RecGroups {
    type DependencyGraph<'a> = HashMap<&'a str, HashSet<&'a str>>;

    fn collect_dependencies<'a>(
      term: &'a Term,
      program: &Program,
      scope: &mut Vec<*const str>,
      deps: &mut HashSet<&'a str>,
    ) {
      match term {
        Term::Var(nam) => {
          if !scope.contains(&(nam.as_str() as *const str)) {
            // We don't care about constructors since they're never recursive.
            if program.funs.contains_key(nam) {
              scope.push(nam.as_str() as *const str);
              deps.insert(nam);
            }
          }
        }
        Term::Lam(nam, bod) => {
          scope.push(nam.as_str() as *const str);
          collect_dependencies(bod, program, scope, deps);
          scope.pop();
        }
        Term::App(fun, arg) => {
          collect_dependencies(fun, program, scope, deps);
          collect_dependencies(arg, program, scope, deps);
        }
        Term::Let(nam, val, bod) => {
          collect_dependencies(val, program, scope, deps);
          scope.push(nam.as_str() as *const str);
          collect_dependencies(bod, program, scope, deps);
          scope.pop();
        }
        Term::Mat(nam, expr, cases) => {
          collect_dependencies(expr, program, scope, deps);
          let adt_nam = program.ctrs.get(&cases[0].0).unwrap();
          let adt = program.adts.get(adt_nam).unwrap();
          for ((_, case), ctr) in cases.iter().zip(adt.ctrs.iter()) {
            let vars =
              ctr.fields.iter().map(|(field, _)| format!("{nam}.{field}")).collect::<Vec<_>>();
            scope.extend(vars.iter().map(|x| x.as_str() as *const str));
            collect_dependencies(case, program, scope, deps);
            scope.truncate(scope.len() - vars.len());
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
    for (name, body) in &program.funs {
      let mut fn_deps = Default::default();
      collect_dependencies(body, program, &mut vec![], &mut fn_deps);
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
    let components = components.into_iter().map(|x| x.into_iter().collect()).collect();
    RecGroups(components)
  }
}

fn infer_program(program: &Program) -> Result<ProgramTypes, String> {
  let rec_groups = RecGroups::from_program(program);
  let mut env = TypeEnv::default();
  let mut types = BTreeMap::new();
  // Add the constructors to the environment.
  for adt in program.adts.values() {
    let adt_t =
      Type::Ctr(adt.name.clone(), adt.vars.iter().map(|var| Type::Var(var.clone())).collect());
    for ctr in adt.ctrs.iter() {
      let ctr_t = ctr
        .fields
        .iter()
        .rfold(adt_t.clone(), |acc, field| Type::Arr(Box::new(field.1.clone()), Box::new(acc)));
      let scheme = ctr_t.generalize(&TypeEnv::default());
      env.0.insert(ctr.name.clone(), scheme);
      types.insert(ctr.name.clone(), ctr_t);
    }
  }
  // Infer the types of regular functions.
  let fn_ts = infer_fns(env, program, rec_groups.0.into_iter(), &mut VarGen::default())?;
  types.extend(fn_ts);
  Ok(ProgramTypes(types))
}

fn infer_fns(
  mut env: TypeEnv,
  program: &Program,
  mut groups: impl Iterator<Item = Vec<String>>,
  var_gen: &mut VarGen,
) -> Result<Vec<(String, Type)>, String> {
  maybe_grow(|| {
    if let Some(group) = groups.next() {
      // Generate fresh type variables for each function in the group.
      let tvs = group.iter().map(|_| var_gen.fresh()).collect::<Vec<_>>();
      for (name, tv) in group.iter().zip(tvs.iter()) {
        env.0.insert(name.clone(), Scheme(vec![], tv.clone()));
      }

      // Infer the types of the functions in the group.
      let mut ss = vec![];
      let mut ts = vec![];
      for name in &group {
        let body = program.funs.get(name).unwrap();
        let (s, t) = infer(&env, program, body, var_gen)?;
        ss.push(s);
        ts.push(t);
      }

      // Unify the inferred body with the corresponding type variable.
      let mut group_s = ss.into_iter().fold(Subst::default(), |s, s2| s.compose(&s2));
      for (bod_t, tv) in ts.into_iter().zip(tvs.iter()) {
        let s = unify(&tv.subst(&group_s), &bod_t)?;
        group_s = s.compose(&group_s);
      }

      // Generalize the function types
      let mut env = env.subst(&group_s);
      let final_ts = tvs.into_iter().map(|tv| tv.subst(&group_s)).collect::<Vec<_>>();
      for (name, t) in group.iter().zip(final_ts.iter()) {
        env.0.insert(name.clone(), t.generalize(&env));
      }

      let rest_ts = infer_fns(env, program, groups, var_gen)?;
      let mut program_types = group.into_iter().zip(final_ts).collect::<Vec<_>>();
      program_types.extend(rest_ts);
      Ok(program_types)
    } else {
      Ok(vec![])
    }
  })
}

/// Infer the type of a term in the given environment.
///
/// The type environment must contain bindings for all the free variables of the term.
///
/// The returned substitution records the type constraints imposed on type variables by the term.
/// The returned type is the type of the term.
fn infer(
  env: &TypeEnv,
  program: &Program,
  term: &Term,
  var_gen: &mut VarGen,
) -> Result<(Subst, Type), String> {
  maybe_grow(|| match term {
    Term::Var(name) => match env.0.get(name) {
      Some(scheme) => {
        let t = scheme.instantiate(var_gen);
        Ok((Subst::default(), t))
      }
      None => Err(format!("unbound variable '{}'", name)),
    },
    Term::Lam(name, body) => {
      let tv = var_gen.fresh();
      let env = env.append(name, Scheme(vec![], tv.clone()));
      let (s, bod_t) = infer(&env, program, body, var_gen)?;
      let var_t = tv.subst(&s);
      Ok((s, Type::Arr(Box::new(var_t), Box::new(bod_t))))
    }
    Term::App(fun, arg) => {
      let (s1, fun_t) = infer(env, program, fun, var_gen)?;
      let (s2, arg_t) = infer(&env.subst(&s1), program, arg, var_gen)?;
      let app_t = var_gen.fresh();
      let s3 = unify(&fun_t.subst(&s2), &Type::Arr(Box::new(arg_t), Box::new(app_t.clone())))?;
      Ok((s3.compose(&s2).compose(&s1), app_t.subst(&s3)))
    }
    Term::Let(name, val, body) => {
      let (s1, val_t) = infer(env, program, val, var_gen)?;
      let bod_env = env.append(name, val_t.generalize(&env.subst(&s1)));
      let (s2, bod_t) = infer(&bod_env, program, body, var_gen)?;
      Ok((s2.compose(&s1), bod_t))
    }
    Term::Mat(scrut, expr, cases) => {
      // Infer type of the scrutinee
      let (s1, t1) = infer(env, program, expr, var_gen)?;

      // Instantiate the expected type of the scrutinee
      let adt_name = program
        .ctrs
        .get(&cases[0].0)
        .ok_or_else(|| format!("Unknown constructor: {}", cases[0].0))?;
      let adt = &program.adts[adt_name];
      let (s2, scrut_t) = instantiate_adt(adt, var_gen)?;

      // Unify the inferred type with the expected type
      let s3 = unify(&t1.subst(&s2), &scrut_t)?;

      // For each case, infer the types and unify them all.
      // Unify the inferred type of the destructured fields with the
      // expected from what we inferred from the scrutinee.
      let s = s3.compose(&s2).compose(&s1);
      let env = env.subst(&s);
      let cases = cases.iter().zip(adt.ctrs.iter()).map(|((_, case), ctr)| (case, ctr));
      infer_match_cases(&env, program, scrut, cases, &s, var_gen)
    }
  })
}

fn instantiate_adt(adt: &Adt, var_gen: &mut VarGen) -> Result<(Subst, Type), String> {
  let tvs = adt.vars.iter().map(|_| var_gen.fresh());
  let s = Subst(adt.vars.iter().zip(tvs).map(|(x, t)| (x.clone(), t)).collect());
  let t = Type::Ctr(adt.name.clone(), adt.vars.iter().cloned().map(Type::Var).collect());
  let t = t.subst(&s);
  Ok((s, t))
}

fn infer_match_cases<'a>(
  env: &TypeEnv,
  program: &'a Program,
  scrut: &'a str,
  mut cases: impl Iterator<Item = (&'a Term, &'a Ctr)>,
  s: &Subst,
  var_gen: &mut VarGen,
) -> Result<(Subst, Type), String> {
  maybe_grow(|| {
    if let Some((bod, ctr)) = cases.next() {
      // One fresh var per field, we later unify with the expected type.
      let tvs = ctr.fields.iter().map(|_| var_gen.fresh()).collect::<Vec<_>>();

      // Add the fields to the environment.
      let vars = ctr.fields.iter().map(|(field, _)| format!("{scrut}.{field}")).collect::<Vec<_>>();
      let mut case_env = env.clone();
      for (field, tv) in vars.iter().zip(tvs.iter()) {
        case_env.0.insert(field.clone(), Scheme(vec![], tv.clone()));
      }

      // Infer the body and unify the inferred field types with the expected.
      let (s1, t1) = infer(&case_env, program, bod, var_gen)?;
      let inf_ts = tvs.into_iter().map(|tv| tv.subst(&s1)).collect::<Vec<_>>();
      let exp_ts = ctr.fields.iter().map(|(_, t)| t.subst(s)).collect::<Vec<_>>();
      let s2 = unify_fields(inf_ts.iter().zip(exp_ts.iter()))?;

      // Recurse and unify with the other arms.
      let (s_rest, t_rest) = infer_match_cases(env, program, scrut, cases, s, var_gen)?;
      let final_s = unify(&t1.subst(&s_rest.compose(&s2)), &t_rest)?;

      Ok((final_s.compose(&s_rest).compose(&s2).compose(&s1).compose(s), t_rest.subst(&final_s)))
    } else {
      let t = var_gen.fresh().subst(s);
      Ok((s.clone(), t))
    }
  })
}

fn unify_fields<'a>(ts: impl Iterator<Item = (&'a Type, &'a Type)>) -> Result<Subst, String> {
  let ss = ts.map(|(inf, exp)| unify(inf, exp)).collect::<Result<Vec<_>, _>>()?;
  let mut s = Subst::default();
  for s2 in ss.into_iter().rev() {
    s = s.compose(&s2);
  }
  Ok(s)
}

fn unify(t1: &Type, t2: &Type) -> Result<Subst, String> {
  maybe_grow(|| match (t1, t2) {
    (Type::Arr(l1, r1), Type::Arr(l2, r2)) => {
      let s1 = unify(l1, l2)?;
      let s2 = unify(&r1.subst(&s1), &r2.subst(&s1))?;
      Ok(s2.compose(&s1))
    }
    (t1, Type::Var(x)) => bind_var(x, t1),
    (Type::Var(x), t2) => bind_var(x, t2),
    (Type::Ctr(name1, ts1), Type::Ctr(name2, ts2)) if name1 == name2 && ts1.len() == ts2.len() => {
      let mut s = Subst::default();
      for (t1, t2) in ts1.iter().zip(ts2.iter()) {
        s = s.compose(&unify(t1, t2)?);
      }
      Ok(s)
    }
    _ => Err(format!("Types do not unify: '{t1}' and '{t2}'")),
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
    Type::Ctr(_, ts) => {
      for t in ts {
        refresh_vars_go(t, map, var_gen);
      }
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
      if self.starts_with("type") {
        let adt = self.parse_adt()?;
        let nam = adt.name.clone();
        let ctrs = adt.ctrs.iter().map(|ctr| ctr.name.clone()).collect::<Vec<_>>();
        for ctr in ctrs {
          program.ctrs.insert(ctr, nam.clone());
        }
        program.adts.insert(nam, adt);
      } else {
        let name = self.parse_name()?;
        self.consume("=")?;
        let term = self.parse_term()?;
        program.funs.insert(name, term);
      }
      self.skip_trivia();
    }
    Ok(program)
  }

  fn parse_adt(&mut self) -> Result<Adt, String> {
    self.consume("type")?;
    self.consume("(")?;
    let name = self.parse_name()?;
    self.skip_trivia();
    let mut vars = Vec::new();
    while !self.starts_with(")") {
      vars.push(self.parse_name()?);
      self.skip_trivia();
    }
    self.consume(")")?;
    self.consume("=")?;
    let mut ctrs = vec![self.parse_ctr()?];
    self.skip_trivia();
    while self.starts_with("|") {
      self.advance_one();
      ctrs.push(self.parse_ctr()?);
      self.skip_trivia();
    }
    Ok(Adt { name, vars, ctrs })
  }

  fn parse_ctr(&mut self) -> Result<Ctr, String> {
    self.consume("(")?;
    let name = self.parse_name()?;
    self.skip_trivia();
    let mut fields = vec![];
    while !self.starts_with(")") {
      let name = self.parse_name()?;
      self.consume(":")?;
      let typ = self.parse_type()?;
      self.skip_trivia();
      let field = (name, typ);
      fields.push(field);
    }
    self.consume(")")?;
    Ok(Ctr { name, fields })
  }

  fn parse_type(&mut self) -> Result<Type, String> {
    maybe_grow(|| {
      self.skip_trivia();
      if self.starts_with("(") {
        // Ctr or Arr
        self.advance_one();
        let head = self.parse_type()?;
        self.skip_trivia();
        if self.starts_with("->") {
          // Arr
          self.consume("->")?;
          let tail = self.parse_type()?;
          Ok(Type::Arr(Box::new(head), Box::new(tail)))
        } else if let Type::Var(name) = head {
          // Ctr
          let mut args = Vec::new();
          while !self.starts_with(")") {
            self.skip_trivia();
            args.push(self.parse_type()?);
            self.skip_trivia();
          }
          self.consume(")")?;
          Ok(Type::Ctr(name, args))
        } else {
          Err(format!("expected ADT name, found {}", head))
        }
      } else {
        // Variable
        let name = self.parse_name()?;
        Ok(Type::Var(name))
      }
    })
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
      } else if self.starts_with("match") {
        // Match
        self.consume("match")?;
        let name = self.parse_name()?;
        self.consume("=")?;
        let expr = self.parse_term()?;
        self.consume("{")?;
        self.skip_trivia();
        let mut cases = Vec::new();
        while !self.starts_with("}") {
          let ctr = self.parse_name()?;
          self.consume(":")?;
          let case = self.parse_term()?;
          cases.push((ctr, case));
          self.skip_trivia();
        }
        self.consume("}")?;
        Ok(Term::Mat(name, Box::new(expr), cases))
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
    for (name, term) in &self.funs {
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
      Term::Mat(name, expr, cases) => {
        write!(f, "match {} = {} {{", name, expr)?;
        for (ctr, case) in cases {
          write!(f, "{}: {} ", ctr, case)?;
        }
        write!(f, "}}")
      }
    })
  }
}

impl std::fmt::Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    maybe_grow(|| match self {
      Type::Var(name) => write!(f, "{}", name),
      Type::Arr(t1, t2) => write!(f, "({} -> {})", t1, t2),
      Type::Ctr(name, ts) => write!(
        f,
        "({}{}{})",
        name,
        if ts.is_empty() { "" } else { " " },
        ts.iter().map(|t| format!("{}", t)).collect::<Vec<_>>().join(" ")
      ),
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
