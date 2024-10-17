module Interpreter.Interpreter where

import Data.List ( find )
-- for debuging don't forget to remove
import Debug.Trace
-- ends here
-- remove when FloatPat Float is FloatPat Double
import GHC.Float (float2Double)

import qualified Syntax.Module as M
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import Syntax.Expression ( LetDecl )
import IO.Error as IOE

data Value = VInt Int
            | VFloat Double
            | VUnit 
            | VChar Char
            | VString String
            | VCons String [Value]
            | VTuple [Value]
            | VFun [([E.Pat], E.RHS)]
            -- do closures capture only the local ctx or also the global?
            | VClosure [E.Pat] E.Exp Context
            | VBuiltin (Value -> Value)

instance Show Value where
  show VUnit = "()"
  show (VInt n) = show n
  show (VFloat n) = show n
  show (VChar c) = show c
  show (VString str) = show str
  show (VCons str vals) = str ++ " " ++ unwords (map show vals)
  show (VTuple tups) = "(" ++ showTups tups ++ ")"
  show (VFun _) = "<fun>"
  show (VClosure _ _ _) = "closure>"
  show (VBuiltin _) = "<builtin>"

showTups :: [Value] -> String
showTups [val] = show val
showTups (val:vals) = show val ++ ", " ++ showTups vals

-- There must be a better way to do this
builtins :: [(String , Value)]
builtins = [
  ("(+)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x + y)))),
  ("(-)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y)))),
  ("(*)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x * y)))),
  ("(/)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y)))),
  ("mod", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (mod x y)))),
  ("negate", VBuiltin (\(VInt x) -> VInt (-x))),
  
  -- TODO: Eww, refactor this
  ("(&&)", VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x && fstToHsBool y)))),
  ("(||)", VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x || fstToHsBool y)))),

  ("(==)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x == y)))),
  ("(/=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x /= y)))),
  ("(>)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x > y)))),
  ("(>=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x >= y)))),
  ("(<)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x < y)))),
  ("(<=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x <= y))))]

-- haskell bool to freest bool
hsToFstBool :: Bool -> Value
hsToFstBool True = VCons "True" []
hsToFstBool False = VCons "False" []

-- freeST bool to haskell bool 
fstToHsBool :: Value -> Bool
fstToHsBool (VCons "True" []) = True
fstToHsBool (VCons "False" []) = False

-- Using a simple context for now for simplicity
type Context = [(String, Value)]

interpret :: M.Module -> Either [IOE.Error] Value
interpret m = case getMainFunction (trace (show m) m) of
  -- Assuming that the RHS of main is always in the form main = <exp>
  -- necessary to initialize the context with information from the module
  -- other modules, prelude, etc
  Just (E.ValDecl _ (E.UnguardedRHS mainExp _)) -> Right $ eval (initContext m ++ builtins, []) mainExp
  -- Return unit when main function is not present
  Nothing -> Right VUnit

getMainFunction :: M.Module -> Maybe LetDecl 
getMainFunction m = find foo (M.definitions m)
  -- main should be a ValDecl VarPat because it is the form main = <body>
  where foo funDef = case funDef of E.ValDecl (E.VarPat _ var) _ -> B.external var == "main"  
                                    _ -> False

-- For now add only definitions to the context.  
initContext :: M.Module -> Context
initContext m =
  -- is VarPat the only valid pattern in a valDecl??
  -- the same for the rhs UnguardedRHS
  map (\def -> case def of E.ValDecl (E.VarPat _ var) (E.UnguardedRHS exp _) -> (B.external var, eval (builtins, []) exp)
                           E.FnDecl var fun -> (B.external var, VFun (map (\(levels, rhs) -> ((map (\(B.ExpLevel pat) -> pat) (filterTypesFromLevels levels)), rhs)) fun))
  -- do not add main to the context
  ) (filter (\def -> case def of E.ValDecl (E.VarPat _ var) _ -> B.external var /= "main" 
                                 E.SigDecl _ _ -> False
                                 _ -> True)
    (M.definitions m))

-- TODO: eval can failed (pattern matching so the return value should be Either [IOE.Error] Value)
-- Global and local context
eval :: (Context, Context) -> E.Exp -> Value
eval _ (E.Int _ n) = VInt n 
eval _ (E.Float _ n) = VFloat n
eval _ (E.Char _ c) = VChar c
eval _ (E.String _ str) = VString str
-- [Exp] -> [Value]
eval ctx (E.Tuple _ tup) = VTuple (map (eval ctx) tup)
-- TODO: implement Constructors with arguments (e.i. data A = B Int | C Float)
eval _ (E.Cons _ (B.Identifier _ str)) = VCons str []
eval ctx (E.Var _ var) = getVar ctx var
eval ctx (E.App _ exp levels) = 
  let args = map (\(B.ExpLevel exp) -> eval ctx exp) (filterTypesFromLevels levels) in
  consumeAllArgs ctx (eval ctx exp) args
eval (_, local) (E.Abs _ levels _ exp) = VClosure (map (\(B.ExpLevel (pat, _)) -> pat) (filterTypesFromLevels levels)) exp local
eval (global, local) (E.Let _ letDecls exp) = eval (global, (resolveLetDecls global (filterTypesFromLetDecls letDecls)) ++ local) exp
eval (global, local) (E.Case _ exp pats) = case chooseCase pats (eval (global, local) exp) of
  Just (exp, matched) -> eval (global, matched ++ local) exp 
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
eval ctx (E.If _ ifExp thenExp elseExp) = if fstToHsBool (eval ctx ifExp) then eval ctx thenExp else eval ctx elseExp
eval _ (E.Channel _ type') = trace ("Channel -> type: " ++ show type') undefined
eval _ (E.Select _ iden) = trace ("Select -> iden: " ++ show iden) undefined

-- interpreter assumes that var fetches can't fail (checks were done before)
-- Eww ungly, find better way of doing this (>>= but the opposite?)
-- TODO: Perguntar ao Gil como é que é utilizado o campo internal das Variable para saber se as posso usar desta maneira
getVar :: (Context, Context) -> B.Variable -> Value
getVar (global, local) var = case find (\(var2, val) -> B.external var == var2) local of
  Just (var, val) -> val
  Nothing -> case find (\(var2, val) -> B.external var == var2) global of
    Just (var, val) -> val
    Nothing -> error ("Variable `" ++ show var ++ "`not found in the context. This should not happen. This is a bug in the compiler")

-- removes the type arguments (i.e. @Int) from arguments
filterTypesFromLevels :: [B.Level a b] -> [B.Level a b]
filterTypesFromLevels = filter (\level -> case level of B.ExpLevel a -> True
                                                        B.TypeLevel b -> False) 

filterTypesFromLetDecls :: [LetDecl] -> [LetDecl]
filterTypesFromLetDecls = filter (\letDecl -> case letDecl of E.ValDecl _ _ -> True
                                                              E.FnDecl _ _ -> True
                                                              E.SigDecl _ _ -> False)

-- Here is where the function application is done.
-- Because of how the parser parses function applications (f a b c d => f [a, b, c, d] even if f only takes one arg)
-- is necessary to repeat the evaluation until [arg] is empty.
-- TODO: context is a mess must check if it is correct, don't like that there is a lot of repetition
consumeAllArgs :: (Context, Context) -> Value -> [Value] -> Value
consumeAllArgs (global, local) (VClosure pats exp local_ctx) args = case sequence (doPatternMatching pats args) of
  Just patternMatching ->
    if length pats == length args then eval (global, patternMatching ++ local_ctx ++ local) exp
    else if length pats < length args then consumeAllArgs (global, patternMatching ++ local_ctx ++ local) (eval (global, patternMatching ++ local_ctx ++ local) exp) (drop (length pats) args)
    else VClosure (drop (length args) pats) exp (patternMatching ++ local_ctx) 
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
consumeAllArgs (global, local) (VFun patExps) args = case chooseRhs patExps args of
  Just (rhs, matched, pats) ->
    let (exp, whereDecls) =
          (case rhs of E.UnguardedRHS exp whereDecls -> (exp, whereDecls)
                       E.GuardedRHS predExps whereDecls ->
                        (case chooseGuard (global, matched) predExps of Just exp -> exp
            -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
                                                                        Nothing -> undefined, whereDecls)) in
    let whereCtx = (case whereDecls of Just letDecls -> resolveLetDecls global letDecls
                                       Nothing -> []) in
    if length pats == length args then eval (global, matched++whereCtx) exp 
    else if length pats < length args then consumeAllArgs (global, matched++whereCtx) (eval (global, matched++whereCtx) exp) (drop (length pats) args)
    else VClosure (drop (length args) pats) exp (matched++whereCtx)
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
-- Is there builtins that take no arguments?
consumeAllArgs ctx (VBuiltin builtin) [] = builtin VUnit
consumeAllArgs ctx (VBuiltin builtin) [arg] = builtin arg
consumeAllArgs ctx (VBuiltin builtin) (arg:args) = consumeAllArgs ctx (builtin arg) args
consumeAllArgs ctx (VCons str vals) args = VCons str (vals++args) 

-- TODO: think of a better name for this function
resolveLetDecls :: Context -> [LetDecl] -> [(String, Value)]
resolveLetDecls _ [] = []
resolveLetDecls global ((E.ValDecl pat rhs):letDecls) = case sequence $ doPatternMatching [pat] [eval (global, whereCtx) exp] of
  Just matched -> matched ++ resolveLetDecls global letDecls
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
  where (exp, whereDecls) = 
          case rhs of E.UnguardedRHS exp whereDecls -> (exp, whereDecls)
                      E.GuardedRHS predExps whereDecls ->
                        (case chooseGuard (global, []) predExps of Just exp -> exp
            -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
                                                                   Nothing -> undefined, whereDecls)
        whereCtx = case whereDecls of Just letDecls -> resolveLetDecls global letDecls

                                      Nothing -> []
resolveLetDecls global ((E.FnDecl var levelRhss):letDecls) = (B.external var, VFun (map (\(levels, rhs) -> ((map (\(B.ExpLevel pat) -> pat) (filterTypesFromLevels levels)), rhs)) levelRhss)) : resolveLetDecls global letDecls

-- TODO: create a resolveWhereDecls for more readable code (Contex -> Maybe [LetDecl] -> [(String, Value)])

-- TODO: refactor to use map and filter?
-- do i need to do Nothing : doPatternMatching pats args or can i just return Nothing
doPatternMatching :: [E.Pat] -> [Value] -> [Maybe (String, Value)]
doPatternMatching [] [] = []
doPatternMatching pats [] = []
doPatternMatching [] args = []
-- TODO: finish implementing the rest of the patterns (ConsPat is partially implemented)
doPatternMatching (pat:pats) (arg:args) = case pat of
  E.WildPat _ _ -> doPatternMatching pats args
  E.VarPat _ var -> Just (B.external var, arg) : doPatternMatching pats args
  E.ConsPat _ (B.Identifier _ pStr) consPats -> let (str, vals) = (\(VCons str vals) -> (str, vals)) arg in
    if str == pStr then doPatternMatching consPats vals ++ doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.TuplePat _ tupPats -> doPatternMatching tupPats ((\(VTuple tupVals) -> tupVals) arg) ++ doPatternMatching pats args
  E.IntPat _ n -> if (\(VInt n) -> n) arg == n then doPatternMatching pats args else Nothing : doPatternMatching pats args 
  E.FloatPat _ n -> if (\(VFloat n) -> n) arg == float2Double n then doPatternMatching pats args else Nothing : doPatternMatching pats args 
  E.CharPat _ c -> if (\(VChar c) -> c) arg == c then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.StringPat _ str -> if (\(VString str) -> str) arg == str then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.AsPat _ var pat2 -> (Just (B.external var, arg)) : doPatternMatching [pat2] [arg] ++ doPatternMatching pats args

chooseRhs :: [([E.Pat], E.RHS)] -> [Value] -> Maybe (E.RHS, [(String, Value)], [E.Pat])
chooseRhs [] _ = Nothing
chooseRhs ((pats, rhs):rest) args = case sequence $ doPatternMatching pats args of
  Just matching -> Just (rhs, matching, pats)
  Nothing -> chooseRhs rest args

chooseCase :: [(E.Pat, E.Exp)] -> Value -> Maybe (E.Exp, [(String, Value)])
chooseCase [] _ = Nothing
chooseCase ((pat, exp):patsExps) val = case doPatternMatching [pat] [val] of
  [] -> Just (exp, [])
  [Just (var, val)] -> Just (exp, [(var, val)])
  [Nothing] -> chooseCase patsExps val

chooseGuard :: (Context, Context) -> [(E.Exp, E.Exp)] -> Maybe E.Exp
chooseGuard _ [] = Nothing 
chooseGuard ctx ((pred, exp):predExps) = if fstToHsBool (eval ctx pred) then Just exp else chooseGuard ctx predExps
