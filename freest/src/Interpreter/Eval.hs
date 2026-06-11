{- |
Module      :  Interpreter.Interpreter
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's interpreter.
-}
module Interpreter.Eval
  (
    interpret
  ) where

{-
TODO:
- Implement channels for case: check https://github.com/freest-lang/freest3/blob/dev/FreeST/src/Interpreter/Eval.hs, evalCase
- When introducing closures, capture only free variables in the environment, and not the whole env
- Handling Prelude definitions, the search in the builtins should be more efficient: check if there's an undefined in the body. Also, what if the user redefines these?
- Handling of undefined is correct?
- Missing evaluation for E.Case (what about labels?)
- Eval can fail due to non-existent patterns during pattern marching. Hence return type should Either [IOE.Error] Value.
 -}

import Control.Concurrent (forkIO)
import Control.Monad (zipWithM, foldM)
import Data.Functor (($>), void)
import Data.List (find)
import Data.Map (empty, singleton, union, unions, lookup, assocs, filterWithKey, insert, fromList)
import Data.Maybe (isJust, fromJust)
import qualified Data.Set as Set
-- for debuging don't forget to remove
import Debug.Trace
-- ends here

import Interpreter.PatternMatching (mkClosure, matchPat, matchClause, forceColumns)
import Interpreter.Values (Env, Clause, Value(..), chan, send, builtins, fstToHsBool, receive, receiveLabel)
import qualified Syntax.Base as B
import qualified Syntax.Expression as E
import qualified Syntax.Module as M
import Utils (internalError)

-- | An alternative of a case expression
type Alternative = (E.Pat, E.KindedRHS)

-- AUXILIARY FUNCTIONS

-- | Bind a clause/alternative's `where` declarations; they are in scope for
-- both the guards and the bodies of the RHS.
bindWhere :: Env -> Maybe [E.KindedLetDecl] -> IO Env
bindWhere env = \case
  Nothing    -> return env
  Just decls -> do
    binds <- collectLetDecls env decls
    return (binds `union` env)

-- | Evaluate guards in order, returning the first body whose guard holds, or
-- 'Nothing' if every guard fails (so matching falls through to the next clause).
tryGuards :: Env -> [(E.KindedExp, E.KindedExp)] -> IO (Maybe E.KindedExp)
tryGuards env = \case
  [] -> return Nothing
  (guard, body) : guards -> do
    val <- eval env guard
    if fstToHsBool val then return (Just body) else tryGuards env guards

-- | Resolve a RHS in an environment that already holds the pattern bindings:
-- bind the `where` declarations, then (for a guarded RHS) select a guard.
-- Returns the chosen body and the environment to evaluate it in, or 'Nothing'
-- if all guards fail.
resolveRHS :: Env -> E.KindedRHS -> IO (Maybe (E.KindedExp, Env))
resolveRHS env = \case
  E.UnguardedRHS body whereDecls -> do
    env' <- bindWhere env whereDecls
    return (Just (body, env'))
  E.GuardedRHS guards whereDecls -> do
    env' <- bindWhere env whereDecls
    mBody <- tryGuards env' guards
    return (fmap (\body -> (body, env')) mBody)

-- | The single matcher shared by functions and @case@ expressions. Tries the
-- clauses in order against the (already-evaluated) argument values: a clause is
-- chosen only if its columns all match *and* its guards succeed; otherwise we
-- fall through to the next clause. The given environment is used to evaluate
-- guards and bodies.
matchClauses :: Env -> [Value] -> [Clause] -> IO Value
matchClauses env vals clauses = do
  -- perform the session effects (receive/branch/wait) once, up front, turning
  -- channels into ordinary data values; then match the clauses purely.
  vals' <- forceColumns clauses vals
  goRows vals' clauses
  where
    goRows vals' = \case
      [] -> errorWithoutStackTrace $
        show (clausesSpan clauses) ++ ": Non-exhaustive patterns in pattern matching"
      (pats, rhs) : rest -> do
        mb <- matchClause pats vals'
        case mb of
          Nothing    -> goRows vals' rest                -- a column failed
          Just binds -> do
            res <- resolveRHS (binds `union` env) rhs
            case res of
              Nothing          -> goRows vals' rest      -- guards failed: fall through
              Just (exp', env') -> eval env' exp'

-- | A source span locating a group of clauses for a non-exhaustive-match error:
-- the whole group, from the head of the first clause to the body of the last.
clausesSpan :: [Clause] -> B.Span
clausesSpan = \case
  []  -> B.nullSpan
  cls -> B.spanFromTo (clauseHead (head cls)) (B.getSpan (snd (last cls)))
  where
    clauseHead = \case
      (p : _, _) -> B.getSpan p
      (_,    rhs) -> B.getSpan rhs



-- | Collect the bindings introduced by a group of declarations, processed
-- top-down (as `let`/`where` are). A binding sees the earlier bindings; a
-- function additionally sees itself (recursion is the default), and the
-- functions of a @mutual@ block see one another. The knots are tied with an
-- ordinary recursive @let@ (@mkClosure@ captures its environment lazily).
--
-- A definition whose name is a builtin (e.g. @(+) = undefined@) is bound to the
-- builtin rather than to its user-written right-hand side.
collectLetDecls :: Env -> [E.KindedLetDecl] -> IO Env
collectLetDecls outer = go outer empty
  where
    -- `env` = outer + the bindings so far; `acc` = just the new bindings
    go :: Env -> Env -> [E.KindedLetDecl] -> IO Env
    go env acc = \case
      [] -> pure acc
      d : ds -> case d of
        E.TypeSig _ _ -> go env acc ds

        -- a single function is recursive in its own name (self-knot)
        E.FnDef var clauses ->
          let val = maybe (mkClosure (insert var val env) (funClauses clauses)) id
                          (Data.Map.lookup (B.external var) builtins)
          in go (insert var val env) (insert var val acc) ds

        -- the functions of a `mutual` block are mutually recursive
        E.Mutual mds ->
          let mbinds    = fromList [ (var, mkClosure mutualEnv (funClauses clauses))
                                   | E.FnDef var clauses <- mds ]
              mutualEnv = env `union` mbinds
          in go mutualEnv (acc `union` mbinds) ds

        -- a value is not recursive: evaluate it in the current environment
        E.ValDef pat rhs
          | Just b <- builtinForPat pat ->
              go (insertVarPat pat b env) (insertVarPat pat b acc) ds
          | otherwise -> do
              res <- resolveRHS env rhs
              (e, env') <- maybe (internalError "Non-exhaustive guards in value definition") pure res
              v     <- eval env' e
              mb    <- matchPat v pat
              binds <- maybe (internalError "Pattern matching failed!") pure mb
              go (binds `union` env) (binds `union` acc) ds

    funClauses = map (\(params, rhs) -> (fst (B.partitionLevels params), rhs))
    builtinForPat = \case
      E.VarPat _ var -> Data.Map.lookup (B.external var) builtins
      _              -> Nothing
    insertVarPat (E.VarPat _ var) val = insert var val
    insertVarPat _                _   = id

-- | Collect declarations from the module, and bind these to variables in an environment
buildEnv :: M.KindedModule -> IO Env
buildEnv m = collectLetDecls empty (M.definitions m)

-- | Lookup a variable in the context
envLookup :: Env -> B.Variable -> Value
envLookup env var =
  case Data.Map.lookup var env of
    Just val -> val
    Nothing -> internalError $ "Variable `" ++ show var ++ "` not found in the context."

-- | Lookup a variable (as a string) in the context
envLookup' :: Env -> String -> Maybe Value
envLookup' env var = do
  let binding = find (\(var', val) -> B.external var' == var) $ assocs env
  case binding of
    Just binding -> return $ snd binding
    Nothing -> Nothing

-- | Evaluate application expressions
handleApplication :: Env -> Value -> [Value] -> IO Value
handleApplication _ func [] = return func
handleApplication _ (VCons cons vals) args = do
  return $ VCons cons $ vals ++ args
handleApplication env (VClosure arity collected clauses cenv) args = do
  let allArgs = collected ++ args
  -- not enough arguments yet: accumulate and stay partially applied
  if length allArgs < arity then
    return $ VClosure arity allArgs clauses cenv
  -- saturated: run the clause matcher on the first `arity` arguments, in the
  -- closure's self-contained captured environment
  else do
    let (these, rest) = splitAt arity allArgs
    result <- matchClauses cenv these clauses
    -- any leftover arguments are applied to the result
    if null rest then return result
    else handleApplication env result rest
handleApplication _ (VBuiltin builtin) args =
  return $ foldl (\(VBuiltin func) arg -> func arg) (VBuiltin builtin) args
handleApplication env VFork [fun] = {- do
  _ <- forkIO $ do
    putStrLn $ "fork started"
    v <- handleApplication env fun [VUnit]
    putStrLn "application handled"
    print v
    putStrLn "value forced"
    pure ()
  pure VUnit -}
  forkIO (void $ handleApplication env fun [VUnit]) $> VUnit
{- handleApplication (global, local) (VSelect label) args =
  case args of
    [VChan chan] -> do
      chan2 <- send (VLabel label) chan
      return $ VChan chan2
    _ -> internalError $ "Too many arguments applied to Select " ++ label ++ "! Type checking failed!" -}
{- handleApplication _ VSendType args =
  case args of
    [VChan chan] -> do
      chan2 <- send VUnit chan
      return $ VChan chan2
    _ -> internalError "Too many arguments applied to SendType! Type checking failed!" -}
{- handleApplication _ VRecvType args =
  case args of
    [VChan chan] -> do
      (_, chan2) <- receive chan
      return $ VChan chan2
    _ -> internalError "Too many arguments applied to ReceiveType! Type checking failed!" -}

-- MAIN FUNCTIONS

-- | Evaluate expressions, encoded as Syntax.Expression.Exp
eval :: Env -> E.KindedExp -> IO Value
eval _ (E.Int _ i) =
  return $ VInt i
eval _ (E.Float _ f) =
  return $ VFloat f
eval _ (E.Char _ c) =
  return $ VChar c
eval _ (E.DCons _ (B.Identifier _ str)) =
  return $ VCons str []
eval env (E.Var _ var) =
  case envLookup env var of
    VIO io -> io
    val -> return val
eval env (E.App _ exp args) = do
  func <- eval env exp
  let termArgs = fst $ B.partitionLevels args
  -- TODO: handle undefined?
  evalArgs <- mapM (eval env) termArgs
  res <- handleApplication env func evalArgs
  case res of
    VIO io -> io
    _ -> return res
eval env (E.Abs _ params _ body) = do
  let expParams = map fst $ fst $ B.partitionLevels params
  -- a lambda is a one-clause function (no guards, no `where`)
  return $ mkClosure env [(expParams, E.UnguardedRHS body Nothing)]
eval env (E.Pack span types exp) = do
  val <- eval env exp
  return $ VPack types val
eval env (E.Asc span exp typ) = do
  eval env exp
eval env (E.Let _ decls exp) = do
  letBindings <- collectLetDecls env decls
  eval (env `union` letBindings) exp
eval env (E.Semi span exp1 exp2) =
  eval env exp1 >> eval env exp2
eval env (E.Case _ exp alternatives) = do
  val <- eval env exp
  -- a `case` is the one-column instance of the clause matcher (session effects,
  -- including choice patterns, are handled inside it)
  matchClauses env [val] (map (\(p, rhs) -> ([p], rhs)) alternatives)
eval env (E.If _ ifExp thenExp elseExp) = do
  ifVal <- eval env ifExp
  if fstToHsBool ifVal
  then eval env thenExp
  else eval env elseExp
eval _ (E.Channel _ _) = do
  -- obtain channel ends for a fresh channel
  (chanL, chanR) <- chan
  return $ VCons "(,)" [VChan chanL, VChan chanR]
eval _ (E.Select _ (B.Identifier _ iden)) = do
  let (Just (VBuiltin selectBuiltin)) = Data.Map.lookup "select" builtins
  return $ selectBuiltin (VLabel iden)
  {- return $ VSelect iden -}
eval _ (E.SendType _ _) =
  return $ fromJust $ Data.Map.lookup "sendType" builtins
  {- return VSendType -}
eval _ (E.ReceiveType _) =
  return $ fromJust $ Data.Map.lookup "receiveType" builtins
  {- return VRecvType -}

-- | Interprets a module and returns the result
interpret :: M.KindedModule -> IO Value
interpret m = do
  -- evaluate module declarations, binding results to variables
  env <- buildEnv m
  let binding = envLookup' env "main"
  -- let binding = find (\(var, val) -> B.external var == "main") $ assocs env
  case binding of
    Just binding -> return binding
    Nothing -> return VUnit
 {-  case getMainFunction m of
    -- main function of the form main = <exp>
    Just (E.ValDef pat rhs) -> do
      (exp, whereDecls) <- extractFromRHS (m_env, empty) rhs
      whereBindings <- case whereDecls of
        Just whereDecls' -> collectLetDecls (m_env, empty) whereDecls'
        Nothing -> return empty
      eval (m_env, whereBindings) exp
    Nothing -> do return VUnit

    getMainFunction m = find (\case E.ValDef (E.VarPat _ var) _ -> B.external var == "main"; _ -> False) (M.definitions m) -}


-- OLD DEFINITIONS

{- -- Here is where the function application is done.
-- Because of how the parser parses function applications (f a b c d => f [a, b, c, d] even if f only takes one arg)
-- is necessary to repeat the evaluation until [arg] is empty.
-- TODO: context is a mess must check if it is correct, don't like that there is a lot of repetition
consumeAllArgs :: (Env, Env) -> Value -> [Value] -> IO Value
consumeAllArgs (global, local) (VClosure pats exp local_ctx) args = case sequence (doPatternMatching pats args []) of
  Just patternMatching ->
    if length pats == length args then eval (global, patternMatching ++ local_ctx ++ local) exp
    else if length pats < length args then do val <- (eval (global, patternMatching ++ local_ctx ++ local) exp)
                                              consumeAllArgs (global, patternMatching ++ local_ctx ++ local) val (drop (length pats) args)
    else return $ VClosure (drop (length args) pats) exp (patternMatching ++ local_ctx)
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
consumeAllArgs (global, local) (VFun patExps) args = do
  labels <- mapM receiveLabel $ getInternalChoiceChannels (fst $ head patExps) args
  case chooseRhs patExps args labels of
    Just (rhs, matched, pats) ->
      do (exp, whereDecls) <- (case rhs of E.UnguardedRHS exp whereDecls -> return (exp, whereDecls)
                                           E.GuardedRHS predExps whereDecls -> do guardsCtx <- chooseGuard (global, matched) predExps
                                                                                  return (guardsCtx, whereDecls))
         let whereCtx = (case whereDecls of Just letDecls -> resolveLetDecls global letDecls
                                            Nothing -> return [])
         whereCtx2 <- whereCtx
         if length pats == length args then eval (global, matched++whereCtx2) exp
         else if length pats < length args then do val <- eval (global, matched++whereCtx2) exp
                                                   consumeAllArgs (global, matched++whereCtx2) val (drop (length pats) args)
         else return $ VClosure (drop (length args) pats) exp (matched++whereCtx2)
    -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
    Nothing -> undefined
-- Is there builtins that take no arguments?
consumeAllArgs ctx (VBuiltin builtin) [] = return $ builtin VUnit
consumeAllArgs ctx (VBuiltin builtin) [arg] = return $ builtin arg
consumeAllArgs ctx (VBuiltin builtin) (arg:args) = consumeAllArgs ctx (builtin arg) args

consumeAllArgs ctx (VCons str vals) args = return $ VCons str (vals++args) -}

{- -- TODO: think of a better name for this function
resolveLetDecls :: Env -> [LetDecl] -> IO [(String, Value)]
resolveLetDecls _ [] = return []
resolveLetDecls global ((E.ValDef pat rhs):letDecls) = do (exp, whereDecls) <- case rhs of
    E.UnguardedRHS exp whereDecls -> return (exp, whereDecls)
    E.GuardedRHS predExps whereDecls -> do 
      guardsCtx <- chooseGuard (global, []) predExps
      return (guardsCtx, whereDecls)
  whereCtx2 <- (case whereDecls of Just letDecls -> resolveLetDecls global letDecls
                                   Nothing -> return [])
  val <- eval (global, whereCtx2) exp
  letDeclsCtx <- resolveLetDecls global letDecls
  return $ case sequence $ doPatternMatching [pat] [val] [] of
    Just matched -> matched ++ letDeclsCtx
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
    Nothing -> undefined

resolveLetDecls global ((E.FnDef var levelRhss):letDecls) = do
  letDeclsCtx <- resolveLetDecls global letDecls
  return $ (B.external var, VFun (map (\(levels, rhs) -> (map (\(B.ExpLevel pat) -> pat) (filterTypesFromLevels levels), rhs)) levelRhss)) : letDeclsCtx -}

-- TODO: create a resolveWhereDecls for more readable code (Env -> Maybe [LetDecl] -> [(String, Value)])

{- -- TODO: DELETE, refactor to use map and filter?
-- do i need to do Nothing : doPatternMatching pats args or can i just return Nothing
doPatternMatching :: [E.Pat] -> [Value] -> [String] -> [Maybe (String, Value)]
doPatternMatching [] [] _ = []
doPatternMatching pats [] _ = []
doPatternMatching [] args _ = []
doPatternMatching (pat:pats) (arg:args) labels = case pat of
  E.WildPat _ _ -> doPatternMatching pats args labels
  E.VarPat _ var -> Just (B.external var, arg) : doPatternMatching pats args labels
  E.DConsPat _ (B.Identifier _ patIden) consPats -> case arg of
    VCons iden consArgs -> if iden == patIden then doPatternMatching consPats consArgs labels ++ doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
    VChan chan -> if patIden == head labels then Just (B.external $ (\[E.VarPat _ var] -> var) consPats, VChan chan) : doPatternMatching pats args (tail labels) else Nothing : doPatternMatching pats args (tail labels)
  -- E.TuplePat _ tupPats -> doPatternMatching tupPats ((\(VTuple tupVals) -> tupVals) arg) ++ doPatternMatching pats args
  E.IntPat _ n -> if (\(VInt n) -> n) arg == n then doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
  E.FloatPat _ n -> if (\(VFloat n) -> n) arg == n then doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
  E.CharPat _ c -> if (\(VChar c) -> c) arg == c then doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
  -- E.StringPat _ str -> if (\(VString str) -> str) arg == str then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.AsPat _ var pat2 -> Just (B.external var, arg) : doPatternMatching [pat2] [arg] labels ++ doPatternMatching pats args labels -}

{- -- necessary to find out if there is an internal choice in the pattern matching to pre receive the label
getInternalChoiceChannels :: [E.Pat] -> [Value] -> [ChannelEnd]
getInternalChoiceChannels [] [] = []
getInternalChoiceChannels pats [] = []
getInternalChoiceChannels [] args = []
getInternalChoiceChannels (pat:pats) (arg:args) = case pat of
  E.DConsPat _ (B.Identifier _ patIden) patCons -> case arg of
    VCons _ consArgs -> getInternalChoiceChannels patCons consArgs ++ getInternalChoiceChannels pats args
    VChan chan -> chan : getInternalChoiceChannels pats args
  _  -> getInternalChoiceChannels pats args
-}