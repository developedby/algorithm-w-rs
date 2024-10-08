{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}

import Control.Applicative ((<|>))
import Control.Arrow (ArrowApply (app))
import Control.Monad (void)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State
import Data.Array (Array, array, (!))
import Data.Char (isAlphaNum, isLetter, isSpace)
import Data.Either (partitionEithers)
import Data.Graph (Graph, Vertex, graphFromEdges, scc)
import Data.List (intercalate, sortOn)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Tree (flatten)
import Data.Type.Coercion (sym)
import Debug.Trace (trace)
import Distribution.TestSuite (TestInstance (name))
import Distribution.Utils.Generic (fstOf3)
import GHC.Generics (C)
import System.Environment (getArgs)
import Text.Parsec qualified as P
import Text.Parsec.String (Parser)

data Program = Program
  { funs :: Funs,
    adts :: ADTs,
    ctrs :: Ctrs
  }

type Funs = Map.Map String Expr

type ADTs = Map.Map String ADT

type Ctrs = Map.Map String String

newtype ProgramTypes = ProgramTypes (Map.Map String Type)

data ADT = ADT String [String] [Constructor]

data Constructor = Constructor String [(String, Type)]

data Expr
  = EVar String
  | ELam String Expr
  | EApp Expr Expr
  | ELet String Expr Expr
  | EMat String Expr [(String, Expr)]

data Type
  = TVar String
  | TArr Type Type
  | TCtr String [Type]
  deriving (Eq)

data Scheme = Scheme [String] Type

type TypeEnv = Map.Map String Scheme

type Subst = Map.Map String Type

type Infer a = ExceptT String (State Int) a

-- A list of all sets of mutually recursive functions.
type RecGroups = [[String]]

-- Substitution application
class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set String

instance Substitutable Type where
  apply s (TVar a) = Map.findWithDefault (TVar a) a s
  apply s (TArr a b) = TArr (apply s a) (apply s b)
  apply s (TCtr name ts) = TCtr name (map (apply s) ts)

  ftv (TVar a) = Set.singleton a
  ftv (TArr a b) = ftv a `Set.union` ftv b
  ftv (TCtr _ ts) = foldr (Set.union . ftv) Set.empty ts

instance Substitutable Scheme where
  apply s (Scheme vars t) = Scheme vars (apply s' t)
    where
      s' = foldr Map.delete s vars

  ftv (Scheme vars t) = ftv t `Set.difference` Set.fromList vars

instance Substitutable TypeEnv where
  apply s = Map.map (apply s)
  ftv :: TypeEnv -> Set.Set String
  ftv = foldr (Set.union . ftv) Set.empty

-- Unifies two types.
unify :: Type -> Type -> Infer Subst
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TArr a b) (TArr a' b') = do
  s1 <- unify a a'
  s2 <- unify (apply s1 b) (apply s1 b')
  return (compose s2 s1)
unify (TCtr name1 args1) (TCtr name2 args2)
  | name1 == name2 && length args1 == length args2 =
      foldM
        (\s (t1, t2) -> compose s <$> unify (apply s t1) (apply s t2))
        Map.empty
        (zip args1 args2)
unify a b = throwError $ "Types do not unify: " ++ show a ++ " and " ++ show b

-- Tries to bind variable `a` to `t` and return that binding as a substitution.
-- Doesn't bind a variable to itself and doesn't bind a variable if it occurs free in `t`.
bind :: String -> Type -> Infer Subst
bind a t
  | t == TVar a = return Map.empty
  | a `Set.member` ftv t = throwError $ "Occurs check fails: " ++ a ++ " occurs free in " ++ show t
  | otherwise = return $ Map.singleton a t

-- Composes two substitutions.
-- Applies the first substitution to the second, and then inserts the result into the first.
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

composeMany :: [Subst] -> Subst
composeMany = foldl compose Map.empty

-- Infers the types of the entire program, for both constructors and functions.
inferProgram :: Program -> RecGroups -> Infer [(String, Type)]
inferProgram program@(Program fns adts ctrs) recGroups = do
  let (env', ctr_ts) = envFromAdts adts
  fns_ts <- inferFns env' program recGroups
  return $ ctr_ts ++ fns_ts
  where
    envFromAdts :: Map.Map String ADT -> (TypeEnv, [(String, Type)])
    envFromAdts adts =
      let adts' = map snd $ Map.toList adts
       in foldl (\(env, ts) adt -> addAdtToEnv env ts adt) (Map.empty, []) adts'

    addAdtToEnv env ts (ADT nam vars ctrs) =
      foldl (\(env, ts) ctr -> addCtrToEnv env ts nam vars ctr) (env, []) ctrs

    addCtrToEnv env ts adt_nam vars (Constructor ctr_nam fields) =
      let ret_t = TCtr adt_nam (map TVar vars)
          ctr_t = foldr (TArr . snd) ret_t fields
          scheme = generalize Map.empty ctr_t
          env' = Map.insert ctr_nam scheme env
          ts' = (ctr_nam, ctr_t) : ts
       in (env', ts')

-- Infers the types of all the functions in the given order.
inferFns :: TypeEnv -> Program -> RecGroups -> Infer [(String, Type)]
inferFns _ _ [] = return []
inferFns env program@(Program fns adts ctrs) (group : rest) = do
  tvs <- mapM (const fresh) group
  let env' = foldr envAppend env (zip group tvs)
  r <- inferGroup env' program group
  let (ss, ts) = unzip r
      unifyGroupElem s (t, tv) = do
        s' <- unify (apply s tv) t
        return (compose s' s)
  s' <- foldM unifyGroupElem (composeMany ss) (zip ts tvs)
  let env' = apply s' env
      ts' = map (apply s') tvs
      schemes = map (generalize env') ts'
      appendFn (name, scheme) = Map.insert name scheme
      env'' = foldr appendFn env' (zip group schemes)
  rest_ts <- inferFns env'' program rest
  return $ zip group ts' ++ rest_ts

inferGroup :: TypeEnv -> Program -> [String] -> Infer [(Subst, Type)]
inferGroup _ _ [] = return []
inferGroup env program@(Program fns adts ctrs) (name : rest) = do
  let expr = fns Map.! name
  (s, t) <- infer env program expr
  res <- inferGroup env program rest
  return $ (s, t) : res

-- Infers the type of a term in the given environment.
infer :: TypeEnv -> Program -> Expr -> Infer (Subst, Type)
infer env program (EVar x) = inferVar env program x
infer env program (ELam x e) = inferLam env program x e
infer env program (EApp e1 e2) = inferApp env program e1 e2
infer env program (ELet nam e1 e2) = inferLet env program nam e1 e2
infer env program (EMat nam e cases) = inferMat env program nam e cases

inferVar env program name = do
  case Map.lookup name env of
    Nothing -> throwError $ "Unbound variable: " ++ name
    Just s -> do
      t <- instantiate s
      return (Map.empty, t)

inferLam env program name body = do
  tv <- fresh
  let env' = envAppend (name, tv) env
  (s1, t1) <- infer env' program body
  return (s1, TArr (apply s1 tv) t1)

inferApp env program e1 e2 = do
  (s1, t1) <- infer env program e1
  (s2, t2) <- infer (apply s1 env) program e2
  tv <- fresh
  s3 <- unify (apply s2 t1) (TArr t2 tv)
  return (composeMany [s3, s2, s1], apply s3 tv)

inferLet env program nam e1 e2 = do
  (s1, t1) <- infer env program e1
  let env' = Map.insert nam (generalize (apply s1 env) t1) env
  (s2, t2) <- infer env' program e2
  return (compose s2 s1, t2)

inferMat env program@(Program fns adts ctrs) scrut e cases = do
  -- Type of match comes from looking up the adt name
  -- Check that all the cases are of the same type
  let (got_ctrs, arms) = unzip cases
      found_adts = map (\x -> fromMaybe "" (Map.lookup x ctrs)) got_ctrs
  when (any (/= head found_adts) found_adts) $
    throwError $
      "Match with diverging types '" ++ show e ++ "'."

  let (ADT nam var exp_ctrs) = adts Map.! head found_adts

  when (any (uncurry (/=)) (zip got_ctrs (map (\(Constructor name _) -> name) exp_ctrs))) $
    throwError $
      "Constructors of " ++ show nam ++ " not in order for '" ++ show e ++ "'."

  (s1, t1) <- infer env program e
  (s2, scrut_t) <- instantiateAdt (ADT nam var exp_ctrs)
  s3 <- unify (apply s2 t1) scrut_t
  let s = composeMany [s3, s2, s1]
      fields = map (\(Constructor _ fields) -> map fst fields) exp_ctrs
      fieldName var field = var ++ "." ++ field
      field_names = map (map (fieldName scrut)) fields
  (s', t) <- inferMatchCases (apply s env) program (zip3 field_names arms exp_ctrs) s
  return (s', t)
  where
    inferMatchCases :: TypeEnv -> Program -> [([String], Expr, Constructor)] -> Subst -> Infer (Subst, Type)
    inferMatchCases env program ((names, e, ctr) : rest) s = do
      let Constructor _ fields = ctr
      let (_, types) = unzip fields
      -- One fresh var per field, we later unify with the expected type.
      tvs <- mapM (const fresh) fields

      -- Add the fields to the environment.
      let env' = foldr envAppend env (zip names tvs)

      -- Infer the body and unify the inferred field types with the expected.
      (s1,  t1) <- infer env' program e
      s2 <- unifyFields (zip (map (apply s1) tvs) (map (apply s) types))

      -- Recurse and unify with the other arms
      (s', t') <- inferMatchCases env program rest s
      s'' <- unify (apply (compose s' s2) t1) t'
      return (composeMany [s'', s', s2, s1, s], apply s'' t')
    inferMatchCases env program [] s = do
      tv <- fresh
      return (s, apply s tv)

    unifyFields :: [(Type, Type)] -> Infer Subst
    unifyFields ((inf, exp) : rest) = do
      s <- unify inf exp
      s' <- unifyFields rest
      return $ compose s s'
    unifyFields [] = return Map.empty

-- Instantiates a polymorphic type with fresh type variables.
instantiate :: Scheme -> Infer Type
instantiate (Scheme vars t) = do
  new <- mapM (const fresh) vars
  let s = Map.fromList (zip vars new)
  return $ apply s t

instantiateAdt :: ADT -> Infer (Subst, Type)
instantiateAdt (ADT name params ctrs) = do
  new <- mapM (const fresh) params
  let s = Map.fromList (zip params new)
  let t = TCtr name (map TVar params)
  return (s, apply s t)

-- Generalizes a monomorphic type by abstracting over the type
-- variables free in `t` but not free in the type environment.
generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toList $ Set.difference (ftv t) (ftv env)

envAppend :: (String, Type) -> TypeEnv -> TypeEnv
envAppend (name, tv) = Map.insert name (Scheme [] tv)

-- Generates a fresh type variable.
fresh :: Infer Type
fresh = do
  s <- get
  put (s + 1)
  return $ TVar ("a" ++ show s)

-- Main inference function
elaborate :: Program -> Either String ProgramTypes
elaborate program = do
  let recGroups = recursionGroups program
  types <- evalState (runExceptT $ inferProgram program recGroups) 0
  return $ refreshProgram (ProgramTypes (Map.fromList types))

-- Search for mutually recursive functions
recursionGroups :: Program -> RecGroups
recursionGroups program@(Program fns _ _) =
  let nodes = Map.toList fns
      (graph, vertexToNode, _) = graphFromEdges [(name, name, collectRefs program [] expr) | (name, expr) <- nodes]
      sccs = scc graph
      addVertex vertex acc = fstOf3 (vertexToNode vertex) : acc
      vertices = map (foldr addVertex []) sccs
   in vertices

collectRefs :: Program -> [String] -> Expr -> [String]
collectRefs (Program funs _ _) scope (EVar name) = [name | Map.member name funs && notElem name scope]
collectRefs program scope (ELam name body) = collectRefs program (name : scope) body
collectRefs program scope (EApp e1 e2) = collectRefs program scope e1 ++ collectRefs program scope e2
collectRefs program scope (ELet name e1 e2) = collectRefs program scope e1 ++ collectRefs program (name : scope) e2
collectRefs program@(Program _ adts ctrs) scope (EMat name scrut cases) =
  let fstCtr = fst $ head cases
      adtNam = ctrs Map.! fstCtr
      (ADT _ _ adtCtrs) = adts Map.! adtNam
      fields = map (\(Constructor _ fields) -> map fst fields) adtCtrs
      vars = map (map (\field -> name ++ "." ++ field)) fields
      collectCase (vars, (_, case')) = collectRefs program (vars ++ scope) case'
   in collectRefs program scope scrut ++ concatMap collectCase (zip vars cases)

-- Type variable refresher

refreshTypeVars :: Type -> State (Map.Map String String) Type
refreshTypeVars (TVar name) = do
  nameMap <- get
  case Map.lookup name nameMap of
    Just newName -> return $ TVar newName
    Nothing -> do
      let newName = "a" ++ show (Map.size nameMap)
      modify (Map.insert name newName)
      return $ TVar newName
refreshTypeVars (TArr t1 t2) = TArr <$> refreshTypeVars t1 <*> refreshTypeVars t2
refreshTypeVars (TCtr name ts) = TCtr name <$> mapM refreshTypeVars ts

refreshProgram :: ProgramTypes -> ProgramTypes
refreshProgram (ProgramTypes types) =
  ProgramTypes $ Map.map refreshFunctionType types
  where
    refreshFunctionType t = evalState (refreshTypeVars t) Map.empty

-- Helper parsers

skipSpacesAndComments :: Parser ()
skipSpacesAndComments =
  void $
    P.many $
      P.choice
        [ void $ P.satisfy isSpace,
          void $ P.try (P.string "//") *> P.manyTill P.anyChar (P.try (P.char '\n'))
        ]

lexeme :: Parser a -> Parser a
lexeme p = p <* skipSpacesAndComments

symbol :: String -> Parser Bool
symbol s = lexeme $ P.string s >> return True

-- Main parsers

parseProgram :: Parser Program
parseProgram = do
  decls <- P.many $ (Left <$> parseAdt) <|> (Right <$> parseFunction)
  let (adts, fns) = partitionEithers decls
      adts' = map (\(ADT name vars ctrs) -> (name, ADT name vars ctrs)) adts
      ctrs = concat [[(ctr_nam, adt_nam) | (Constructor ctr_nam _) <- ctrs] | (ADT adt_nam _ ctrs) <- adts]
  return $ Program (Map.fromList fns) (Map.fromList adts') (Map.fromList ctrs)

parseAdt :: Parser ADT
parseAdt = P.try $ do
  symbol "type"
  symbol "("
  name <- parseName
  vars <- P.many parseName
  symbol ")"
  symbol "="
  ctrs <- P.sepBy1 parseCtr (symbol "|")
  return $ ADT name vars ctrs

parseCtr :: Parser Constructor
parseCtr = do
  symbol "("
  name <- parseName
  let parseField = do
        name <- parseName
        symbol ":"
        typ <- parseType
        return (name, typ)
  fields <- P.many parseField
  symbol ")"
  return $ Constructor name fields

parseFunction :: Parser (String, Expr)
parseFunction = do
  name <- parseName
  symbol "="
  term <- parseExpr
  return (name, term)

parseExpr :: Parser Expr
parseExpr =
  parseELet
    <|> parseEMat
    <|> parseELam
    <|> parseEApp
    <|> parseEVar

parseELet :: Parser Expr
parseELet = do
  P.try $ symbol "let"
  name <- parseName
  symbol "="
  val <- parseExpr
  symbol ";"
  body <- parseExpr
  return $ ELet name val body

parseELam :: Parser Expr
parseELam = do
  P.try $ symbol "λ" <|> symbol "@"
  name <- parseName
  body <- parseExpr
  return $ ELam name body

parseEApp :: Parser Expr
parseEApp = P.try $ do
  symbol "("
  terms <- P.many1 parseExpr
  symbol ")"
  return $ foldl1 EApp terms

parseEVar :: Parser Expr
parseEVar = EVar <$> parseName

parseEMat :: Parser Expr
parseEMat = do
  P.try $ symbol "match"
  name <- parseName
  symbol "="
  e <- parseExpr
  symbol "{"
  cases <- P.many $ do
    ctr <- parseName
    symbol ":"
    body <- parseExpr
    return (ctr, body)
  symbol "}"
  return $ EMat name e cases

parseType :: Parser Type
parseType = P.choice [parseArrType, parseCtrType, parseVarType]

parseVarType :: Parser Type
parseVarType = TVar <$> parseName

parseArrType :: Parser Type
parseArrType = P.try $ do
  symbol "("
  t1 <- parseType
  symbol "->"
  t2 <- parseType
  symbol ")"
  return $ TArr t1 t2

parseCtrType :: Parser Type
parseCtrType = P.try $ do
  symbol "("
  name <- parseName
  ts <- P.many parseType
  symbol ")"
  return $ TCtr name ts

parseName :: Parser String
parseName = lexeme $ (:) <$> P.satisfy isFirstChar <*> P.many (P.satisfy isRestChar)
  where
    isFirstChar c = isLetter c || c == '_' || c == '.'
    isRestChar c = isAlphaNum c || c == '_' || c == '.' || c == '/'

-- Helper functions

parseFromString :: Parser a -> String -> Either P.ParseError a
parseFromString p = P.parse (p <* P.eof) ""

instance Read Expr where
  readsPrec _ input =
    case parseFromString parseExpr input of
      Left _ -> []
      Right term -> [(term, "")]

instance Read Program where
  readsPrec _ input =
    case parseFromString parseProgram input of
      Left _ -> []
      Right program -> [(program, "")]

-- Display functions

instance Show Program where
  show (Program fns adts ctrs) =
    -- show ADTs and then functions
    unlines [show adt | adt <- Map.elems adts]
      ++ "\n"
      ++ unlines [name ++ " = " ++ show expr | (name, expr) <- Map.toList fns]

instance Show ADT where
  show (ADT name vars ctrs) = "type (" ++ unwords (name : vars) ++ ") = " ++ intercalate " | " [show c | c <- ctrs]

instance Show Constructor where
  show (Constructor name types) =
    let showField (name, typ) = name ++ ": " ++ show typ
     in "(" ++ unwords (name : map showField types) ++ ")"

instance Show Expr where
  show (EVar name) = name
  show (ELam name body) = "λ" ++ name ++ " " ++ show body
  show (EApp fun arg) = "(" ++ show fun ++ " " ++ show arg ++ ")"
  show (ELet name val body) = "let " ++ name ++ " = " ++ show val ++ "; " ++ show body
  show (EMat name e cases) =
    let showCase (ctr, body) = ctr ++ ": " ++ show body
     in "match " ++ name ++ " = " ++ show e ++ " { " ++ unwords (map showCase cases) ++ " }"

instance Show Type where
  show (TVar name) = name
  show (TArr t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TCtr name ts) = "(" ++ unwords (name : map show ts) ++ ")"

instance Show Scheme where
  show (Scheme vars t) = concat ["∀" ++ v ++ " " | v <- vars] ++ show t

instance Show ProgramTypes where
  show (ProgramTypes types) =
    unlines $ map showType $ sortOn fst $ Map.toList types
    where
      showType (name, t) = name ++ " : " ++ show t

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName] -> do
      content <- TIO.readFile fileName
      case parseFromString parseProgram (T.unpack content) of
        Left err -> putStrLn $ "Parse error: " ++ show err
        Right program@(Program fns adts ctrs) -> do
          putStrLn "Parsed program:"
          print program
          putStrLn $ "Recursion groups: " ++ show (recursionGroups program)
          putStrLn "\nInferred types:"
          case elaborate program of
            Left err -> putStrLn $ "Type inference error: " ++ err
            Right programTypes -> print programTypes
    _ -> putStrLn "Usage: program <filename>"
