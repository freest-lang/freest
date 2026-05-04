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
- Handling Prelude definitions, the search in the builtins should be more efficient: check if there's an undefined in the body.
- Handling of undefined is correct?
- Missing evaluation for E.Pack, E.Case (what about labels?), SendType, ReceiveType
- About SendType and ReceiveType, do we need to define sending and receiving operations?
- Eval can fail due to non-existent patterns during pattern marching. Hence return type should Either [IOE.Error] Value.
-}

import Data.List (find, groupBy)
import Data.Set qualified as Set
import Data.Map (empty, singleton, union, unions, lookup)
import Data.Maybe (isJust)
import Control.Concurrent (forkIO)
import Control.Monad (zipWithM)
-- for debuging don't forget to remove
import Debug.Trace
-- ends here

import Interpreter.PatternMatching (compileFunctionToClosure, resolvePatternMatching)
import Interpreter.Values (Env, Value(..), chan, send, builtins, fstToHsBool)
import qualified Syntax.Base as B
import qualified Syntax.Expression as E
import qualified Syntax.Module as M

import Syntax.Expression ( KindedLetDecl )
import qualified Syntax.Module as N

type GlobalEnv = Env
type LocalEnv = Env

-- | An alternative of a case expression
type Alternative = (E.Pat, E.KindedRHS)

-- AUXILIARY FUNCTIONS

-- | Choose the correct guard via evaluation
chooseGuard :: (GlobalEnv, LocalEnv) -> [(E.KindedExp, E.KindedExp)] -> IO E.KindedExp
chooseGuard _ [] = error "Non-exaustive guards!"
chooseGuard env ((guard, exp):guards) = do
  val <- eval env guard
  if fstToHsBool val then return exp else chooseGuard env guards

-- | Choose the correct alternative, matching it against an argument via pattern matching
chooseCase :: [Alternative] -> Value -> Maybe (Alternative, Env)
chooseCase [] _ = Nothing
chooseCase ((pat, rhs) : alternatives) val =
  -- try to match pattern and argument through pattern matching
  case resolvePatternMatching pat val of
    Left _ -> chooseCase alternatives val
    Right bindings -> Just ((pat, rhs), bindings)

-- | Extract an expression and let declarations from case alternatives
extractFromRHS :: (GlobalEnv, LocalEnv) -> E.KindedRHS -> IO (E.KindedExp, Maybe [KindedLetDecl])
extractFromRHS (global, local) rhs = do
  -- extract expression and where declarations from either guarded or unguarded rhs
  case rhs of
    E.UnguardedRHS exp whereDecls -> return (exp, whereDecls)
    E.GuardedRHS guards whereDecls -> do
      exp <- chooseGuard (global, local) guards
      return (exp, whereDecls)

-- | Collect bindings, of variables to values, from declarations
collectLetDecls :: (GlobalEnv, LocalEnv) -> [KindedLetDecl] -> IO Env
collectLetDecls _ [] = return empty
collectLetDecls (global, local) ((E.ValDef pat rhs) : letdecls)
  -- bind builtin value declaration to corresponding value in Values.builtins
  -- TODO: inefficient since it searches for all variables if it exists in builtins; try to only search those that call undefined
  | isVarPat pat && isJust (Data.Map.lookup (B.external $ getVarPat pat) builtins) = do
    let var = getVarPat pat
    let (Just value) = Data.Map.lookup (B.external var) builtins
    let binding = singleton var value
    remainingBindings <- collectLetDecls (binding `union` global, local) letdecls
    return $ binding `union` remainingBindings
  | otherwise = do
    -- extract expression and where declarations from either guarded or unguarded rhs
    (exp, whereDecls) <- extractFromRHS (global, local) rhs
    -- get bindings from where declaration
    whereBindings <- case whereDecls of
      Just whereDecls' -> collectLetDecls (global, local) whereDecls'
      Nothing -> return empty
    -- evaluate expression
    val <- eval (global, whereBindings `union` local) exp
    -- resolve pattern matching to match variables from pattern to the value from rhs
    let patternMatchRes = resolvePatternMatching pat val
    bindings <- case patternMatchRes of
      Left _ -> error "Pattern matching failed!"
      Right bindings -> return bindings
    -- collect the rest of the let declarations, inserting into the environment the bindings obtained from the first expression
    remainingBindings <- collectLetDecls (global, bindings `union` local) letdecls
    return $ bindings `union` remainingBindings
  where
    isVarPat :: E.Pat -> Bool
    isVarPat (E.VarPat _ var) = True
    isVarPat _                = False
    getVarPat :: E.Pat -> B.Variable
    getVarPat (E.VarPat _ var) = var
collectLetDecls (global, local) ((E.FnDef var clauses) : letdecls)
  -- bind builtin function declaration to corresponding value in Values.builtins
  -- TODO: inefficient since it searches for all variables if it exists in builtins; try to only search those that call undefined
  | isJust $ Data.Map.lookup var.external builtins = do
    let (Just value) = Data.Map.lookup var.external builtins
    let binding = singleton var value
    remainingBindings <- collectLetDecls (binding `union` global, local) letdecls
    return $ binding `union` remainingBindings
  | otherwise = do
    -- remove type arguments from clauses
    let clauses' = map (\(params, body) -> (map (\(B.ExpLevel pat) -> pat) $ filter (\case B.ExpLevel a -> True; B.TypeLevel b -> False) params, body)) clauses
    -- create binding for function
    let binding = singleton var (compileFunctionToClosure clauses')
    remainingBindings <- collectLetDecls (global, binding `union` local) letdecls
    return $ binding `union` remainingBindings
collectLetDecls (global, local) ((E.Mutual mutualDecls) : letdecls) = error "Evaluation of E.LetDecl Mutual not implemented"

-- | Obtain the main function from a module.
getMainFunction :: M.KindedModule -> Maybe KindedLetDecl
getMainFunction m = find (\case E.ValDef (E.VarPat _ var) _ -> B.external var == "main"; _ -> False) (M.definitions m)

-- | Collect declarations from the module, and bind these to variables in an environment
buildEnv :: M.KindedModule -> IO Env
buildEnv m = collectLetDecls (empty, empty) letDecls
  -- obtain all let declarations from the module except the main function and those related to kinds / types
  where letDecls = filter (\case
          E.ValDef (E.VarPat _ var) _ -> B.external var /= "main"
          E.TypeSig _ _ -> False
          _ -> True) (M.definitions m)

-- | Lookup a variable in both local and global context, in that order
envLookup :: (GlobalEnv, LocalEnv) -> B.Variable -> Value
envLookup _ (B.Variable{B.varSpan=_, B.internal=_, B.external="fork"}) = VFork
envLookup (global, local) var =
  -- search in local context first
  case Data.Map.lookup var local of
    Just val -> val
    -- search in global context after
    Nothing -> case Data.Map.lookup var global of
      Just val -> val
      Nothing -> error ("Variable `" ++ show var ++ "` not found in the context." ++
                       " This should not happen. This is a bug in the compiler")

-- | Evaluate application expressions
handleApplication :: (GlobalEnv, LocalEnv) -> Value -> [Value] -> IO Value
handleApplication (global, local) (VCons cons vals) args = do
  return $ VCons cons $ vals ++ args
-- application of closure to arguments
handleApplication (global, local) (VClosure pats body env) args = do
  -- get the number of parameters and arguments
  let numParams = length pats
      numArgs = length args
  
  -- if there's not enough arguments, partially apply
  if numParams > numArgs then do
    -- extract bindings through pattern matching
    -- use only the necessary parameters
    case zipWithM resolvePatternMatching (take numArgs pats) args of
          Left _ -> error "Pattern matching failed!"
          Right bindings ->
            -- create a new closure with the remaining parameters
            return $ VClosure (drop (numParams - numArgs) pats) body $ unions bindings `union` env

  -- if numParams <= numArgs, evaluate app, return app against remaining arguments
  else do
    -- extract bindings through pattern matching
    -- use only the necessary arguments
    case zipWithM resolvePatternMatching pats (take numParams args) of
          Left _ -> error "Pattern matching failed!"
          Right bindings -> do
            -- evaluate application of closure against arguments
            func <- eval (global, unions bindings `union` env) body
            -- the number of arguments is the same as parameters, return result of evaluation
            if numArgs == numParams then
              return func
            -- otherwise, create a new application with the remaining arguments
            else handleApplication (global, local) func (drop (numArgs - numParams) args)  
-- application of builtins to arguments
handleApplication (global, local) (VBuiltin builtin) args =
  return $ foldl (\(VBuiltin func) arg -> func arg) (VBuiltin builtin) args
handleApplication (global, local) VFork args =
  error "Evaluation of application between VFork and args not implemented"
{-     VFork -> forkIO (void $ consumeAllArgs (global, []) (head args) [VUnit]) $> VUnit
    _ -> do res <- consumeAllArgs (global, local) left args
            case res of
              VIO io -> io
              _ -> return res -}
handleApplication _ (VSelect label) args =
  case args of
    -- application of select with a channel
    [VChan chan] -> do
      chan2 <- send (VLabel label) chan
      return $ VChan chan2
    -- otherwise
    _ -> error $ "Too many arguments applied to Select " ++ label ++ "! Type checking failed!"

-- MAIN FUNCTIONS

-- | Evaluate expressions, encoded as Syntax.Expression.Exp
eval :: (GlobalEnv, LocalEnv) -> E.KindedExp -> IO Value
eval _ (E.Int _ i) =
  return $ VInt i
eval _ (E.Float _ f) =
  return $ VFloat f
eval _ (E.Char _ c) =
  return $ VChar c
eval _ (E.DCons _ (B.Identifier _ str)) =
  return $ VCons str []
eval (global, local) (E.Var _ var) =
  case envLookup (global, local) var of
    VIO io -> io
    val -> return val
eval (global, local) (E.App _ exp args) = do
  -- evaluate left expression
  func <- eval (global, local) exp
  -- remove type arguments, as these are not useful during reduction
  let expArgs = filter (\case B.ExpLevel a -> True; B.TypeLevel b -> False) args
  -- handle undefined
  -- evaluate arguments
  evalArgs <- mapM (\(B.ExpLevel exp') -> eval (global, local) exp') expArgs
  handleApplication (global, local) func evalArgs
eval (_, local) (E.Abs _ params _ body) =
  -- remove type parameters, as these are not useful during reduction
  let expParams = filter (\case B.ExpLevel a -> True; B.TypeLevel b -> False) params
  -- convert to a closure, capturing the local environment, so we don't lose bindings
  in return $ VClosure (map (\(B.ExpLevel (pat, _)) -> pat) expParams) body local
eval (global, local) (E.Pack span types exp) = 
  error "Evaluation of E.Pack not implemented"
eval (global, local) (E.Asc span exp typ) =
  eval (global, local) exp
eval (global, local) (E.Let _ decls exp) = do
  -- remove type signature declarations
  let expDecls = filter (\case E.TypeSig _ _ -> False; _ -> True) decls
  letBindings <- collectLetDecls (global, local) expDecls
  eval (global, letBindings `union` local) exp
eval (global, local) (E.Semi span exp1 exp2) =
  eval (global, local) exp1 >> eval (global, local) exp2
eval (global, local) (E.Case _ exp alternatives) = do
  val <- eval (global, local) exp
  case chooseCase alternatives val of
    Nothing -> error "Non-exaustive patterns in case alternatives"
    Just (alternative, bindings) -> do
      -- extract expression and where declarations from either guarded or unguarded rhs
      (exp', whereDecls) <- extractFromRHS (global, bindings `union` local) (snd alternative)
      -- get bindings from where declaration
      whereBindings <- case whereDecls of
        Just whereDecls' -> collectLetDecls (global, bindings `union` local) whereDecls'
        Nothing -> return empty
      eval (global, whereBindings `union` bindings `union` local) exp'      
  {- do
  labels <- mapM receiveLabel $ getInternalChoiceChannels [fst $ head pats] [val]
  case chooseCase pats val labels of
    Just (exp, matched) -> eval (global, matched ++ local) exp 
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
    Nothing -> undefined -}
eval env (E.If _ ifExp thenExp elseExp) = do
  ifVal <- eval env ifExp
  thenVal <- eval env thenExp
  elseVal <- eval env elseExp
  if fstToHsBool ifVal then return thenVal else return elseVal
eval _ (E.Channel _ _) = do
  -- obtain channel ends for a fresh channel
  (chanL, chanR) <- chan
  return $ VCons "(,)" [VChan chanL, VChan chanR]
eval ctx (E.Select _ (B.Identifier _ iden)) =
  return $ VSelect iden
eval (global, local) (E.SendType span typ) = 
  error "Evaluation of E.SendType not implemented"
eval (global, local) (E.ReceiveType span) = 
  error "Evaluation of E.ReceiveType not implemented"

-- | Interprets a module and returns the result
interpret :: M.KindedModule -> IO Value
interpret m = do
  -- collect module declarations, forming the initial environment
  m_env <- buildEnv m
  case getMainFunction m of
    -- main function of the form main = <exp>
    Just (E.ValDef pat rhs) -> do
      -- extract expression and where declarations from either guarded or unguarded rhs
      (exp, whereDecls) <- extractFromRHS (m_env, empty) rhs
      -- get bindings from where declaration
      whereBindings <- case whereDecls of
        Just whereDecls' -> collectLetDecls (m_env, empty) whereDecls'
        Nothing -> return empty
      eval (m_env, whereBindings) exp
    -- if main function is not present, return unit
    Nothing -> do return VUnit

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