{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}

import Control.Applicative ((<|>))
import Control.Monad (void)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State
import Data.Array (Array, array, (!))
import Data.Char (isAlphaNum, isLetter, isSpace)
import Data.Graph (Graph, Vertex, topSort)
import Data.List (sortOn)
import Data.Map qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Tree (flatten)
import System.Environment (getArgs)
import Text.Parsec qualified as P
import Text.Parsec.String (Parser)

newtype Program = Program (Map.Map String Expr)

newtype ProgramTypes = ProgramTypes (Map.Map String Type)

data Expr
  = EVar String
  | ELam String Expr
  | EApp Expr Expr
  | ELet String Expr Expr

data Type
  = TVar String
  | TArr Type Type
  deriving (Eq)

data Scheme = Scheme [String] Type

type TypeEnv = Map.Map String Scheme

type Subst = Map.Map String Type

type Infer a = ExceptT String (State Int) a

-- Substitution application
class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set String

instance Substitutable Type where
  apply s (TVar a) = Map.findWithDefault (TVar a) a s
  apply s (TArr a b) = TArr (apply s a) (apply s b)

  ftv (TVar a) = Set.singleton a
  ftv (TArr a b) = ftv a `Set.union` ftv b

instance Substitutable Scheme where
  apply s (Scheme vars t) = Scheme vars (apply s' t)
    where
      s' = foldr Map.delete s vars

  ftv (Scheme vars t) = ftv t `Set.difference` Set.fromList vars

instance Substitutable TypeEnv where
  apply s = Map.map (apply s)
  ftv = foldr (Set.union . ftv) Set.empty

-- Unifies two types.
unify :: Type -> Type -> Infer Subst
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TArr a b) (TArr a' b') = do
  s1 <- unify a a'
  s2 <- unify (apply s1 b) (apply s1 b')
  return (compose s2 s1)
unify _ _ = throwError "Types do not unify"

-- Tries to bind variable `a` to `t` and return that binding as a substitution.
-- Doesn't bind a variable to itself and doesn't bind a variable if it occurs free in `t`.
bind :: String -> Type -> Infer Subst
bind a t
  | t == TVar a = return Map.empty
  | a `Set.member` ftv t = throwError "Occurs check fails"
  | otherwise = return $ Map.singleton a t

-- Composes two substitutions.
-- Applies the first substitution to the second, and then inserts the result into the first.
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- Infers the type of a term in the given environment.
infer :: TypeEnv -> Expr -> Infer (Subst, Type)
infer env (EVar x) =
  case Map.lookup x env of
    Nothing -> throwError $ "Unbound variable: " ++ x
    Just s -> do
      t <- instantiate s
      return (Map.empty, t)
infer env (ELam x e) = do
  tv <- fresh
  let env' = Map.insert x (Scheme [] tv) env
  (s1, t1) <- infer env' e
  return (s1, TArr (apply s1 tv) t1)
infer env (EApp e1 e2) = do
  (s1, t1) <- infer env e1
  (s2, t2) <- infer (apply s1 env) e2
  tv <- fresh
  s3 <- unify (apply s2 t1) (TArr t2 tv)
  return (compose (compose s3 s2) s1, apply s3 tv)
infer env (ELet x e1 e2) = do
  (s1, t1) <- infer env e1
  let env' = Map.insert x (generalize (apply s1 env) t1) env
  (s2, t2) <- infer env' e2
  return (compose s2 s1, t2)

-- Instantiates a polymorphic type with fresh type variables.
instantiate :: Scheme -> Infer Type
instantiate (Scheme vars t) = do
  new <- mapM (const fresh) vars
  let s = Map.fromList (zip vars new)
  return $ apply s t

-- Generalizes a monomorphic type by abstracting over the type
-- variables free in `t` but not free in the type environment.
generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toList $ Set.difference (ftv t) (ftv env)

-- Generates a fresh type variable.
fresh :: Infer Type
fresh = do
  s <- get
  put (s + 1)
  return $ TVar ("a" ++ show s)

-- Main inference function
typeInference :: Expr -> Either String Type
typeInference term =
  evalState
    ( runExceptT $ do
        (subst, t) <- infer Map.empty term
        return $ apply subst t
    )
    0

elaborate :: Program -> Either String ProgramTypes
elaborate program@(Program fns) = do
  let order = topologicalOrder program
  types <- inferProgram Map.empty fns order
  return $ refreshProgram (ProgramTypes (Map.fromList types))

inferProgram :: TypeEnv -> Map.Map String Expr -> [String] -> Either String [(String, Type)]
inferProgram _ _ [] = Right []
inferProgram env fns (name : rest) = do
  case Map.lookup name fns of
    Nothing -> Left $ "Function not found: " ++ name
    Just expr -> do
      (_, t) <- evalState (runExceptT $ infer env expr) 0
      let scheme = generalize env t
          env' = Map.insert name scheme env
      rest_types <- inferProgram env' fns rest
      return $ (name, t) : rest_types

-- Topological sort
buildDependencyGraph :: Program -> (Graph, Vertex -> (String, String, [String]))
buildDependencyGraph (Program fns) =
  let nodes = Map.toList fns
      numbered = zip [0 ..] nodes
      lookupVertex name = lookup name (map (\(v, (n, _)) -> (n, v)) numbered)
      vertexToNode v = let (name, expr) = nodes !! v in (name, name, getEdges (name, expr))
      getEdges (_, expr) = collectReferences expr
      graph =
        array
          (0, length nodes - 1)
          [ (v, maybe [] (catMaybes . map lookupVertex . getEdges) (lookup v numbered))
            | v <- [0 .. length nodes - 1]
          ]
   in (graph, vertexToNode)
  where
    collectReferences :: Expr -> [String]
    collectReferences (EVar name) = [name | Map.member name fns]
    collectReferences (ELam _ body) = collectReferences body
    collectReferences (EApp e1 e2) = collectReferences e1 ++ collectReferences e2
    collectReferences (ELet _ e1 e2) = collectReferences e1 ++ collectReferences e2

topologicalOrder :: Program -> [String]
topologicalOrder program =
  let (graph, vertexToNode) = buildDependencyGraph program
   in reverse $ map (\v -> let (name, _, _) = vertexToNode v in name) $ topSort graph

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

refreshProgram :: ProgramTypes -> ProgramTypes
refreshProgram (ProgramTypes types) =
  ProgramTypes $ Map.map refreshFunctionType types
  where
    refreshFunctionType t = evalState (refreshTypeVars t) Map.empty

-- Helper parsers

skipSpaces :: Parser ()
skipSpaces = void $ P.many $ P.satisfy isSpace

lexeme :: Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol :: String -> Parser String
symbol s = lexeme $ P.string s

parens :: Parser a -> Parser a
parens = P.between (symbol "(") (symbol ")")

-- Main parsers

parseProgram :: Parser Program
parseProgram = do
  skipSpaces
  fns <- P.many parseFunction
  return $ Program $ Map.fromList fns

parseFunction :: Parser (String, Expr)
parseFunction = do
  name <- parseName
  symbol "="
  term <- parseTerm
  return (name, term)

parseTerm :: Parser Expr
parseTerm =
  parseLetTerm
    <|> parseLambdaTerm
    <|> parseAppTerm
    <|> parseVarTerm

parseLetTerm :: Parser Expr
parseLetTerm = do
  symbol "let"
  name <- parseName
  symbol "="
  val <- parseTerm
  symbol ";"
  body <- parseTerm
  return $ ELet name val body

parseLambdaTerm :: Parser Expr
parseLambdaTerm = do
  symbol "λ" <|> symbol "@"
  name <- parseName
  body <- parseTerm
  return $ ELam name body

parseAppTerm :: Parser Expr
parseAppTerm = parens $ do
  terms <- P.many1 parseTerm
  return $ foldl1 EApp terms

parseVarTerm :: Parser Expr
parseVarTerm = EVar <$> parseName

parseName :: Parser String
parseName = lexeme $ (:) <$> P.satisfy isFirstChar <*> P.many (P.satisfy isRestChar)
  where
    isFirstChar c = isLetter c || c == '_'
    isRestChar c = isAlphaNum c || c == '_'

-- Helper functions

parseFromString :: Parser a -> String -> Either P.ParseError a
parseFromString p = P.parse (p <* P.eof) ""

instance Read Expr where
  readsPrec _ input =
    case parseFromString parseTerm input of
      Left _ -> []
      Right term -> [(term, "")]

instance Read Program where
  readsPrec _ input =
    case parseFromString parseProgram input of
      Left _ -> []
      Right program -> [(program, "")]

-- Display functions

instance Show Program where
  show (Program fns) = unlines [name ++ " = " ++ show term | (name, term) <- Map.toList fns]

instance Show Expr where
  show (EVar name) = name
  show (ELam name body) = "λ" ++ name ++ " " ++ show body
  show (EApp fun arg) = "(" ++ show fun ++ " " ++ show arg ++ ")"
  show (ELet name val body) = "(let " ++ name ++ " = " ++ show val ++ "; " ++ show body ++ ")"

instance Show Type where
  show (TVar name) = name
  show (TArr t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

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
        Right program -> do
          putStrLn "Parsed program:"
          print program
          putStrLn "\nInferred types:"
          case elaborate program of
            Left err -> putStrLn $ "Type inference error: " ++ err
            Right programTypes -> print programTypes
    _ -> putStrLn "Usage: program <filename>"
