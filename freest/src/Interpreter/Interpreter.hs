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
            | VCons String
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
  show (VCons str) = show str
  show (VFun _) = "<fun>"
  show (VClosure _ _ _) = "closure>"
  show (VBuiltin _) = "<builtin>"

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
  ("(&&)", VBuiltin (\x -> VBuiltin (\y -> hsToFstBool ((fstToHsBool x) && (fstToHsBool y))))),
  ("(||)", VBuiltin (\x -> VBuiltin (\y -> hsToFstBool ((fstToHsBool x) || (fstToHsBool y))))),

  ("(==)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x == y)))),
  ("(/=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x /= y)))),
  ("(>)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x > y)))),
  ("(>=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x >= y)))),
  ("(<)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x < y)))),
  ("(<=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x <= y))))]

-- haskell bool to freest bool
hsToFstBool :: Bool -> Value
hsToFstBool True = VCons "True"
hsToFstBool False = VCons "False"

-- freeST bool to haskell bool 
fstToHsBool :: Value -> Bool
fstToHsBool (VCons "True") = True
fstToHsBool (VCons "False") = False

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
eval _ (E.Cons _ (B.Identifier _ str)) = VCons str
eval ctx (E.Var _ var) = getVar ctx var
eval ctx (E.App _ exp levels) = 
  -- trace ("App -> exp: " ++ (show exp) ++ " level: " ++ (show level) ++ " | Ctx: " ++ (show ctx))
  let args = map (\(B.ExpLevel exp) -> eval ctx exp) (filterTypesFromLevels levels) in
  consumeAllArgs ctx (eval ctx exp) args
-- eval _ _ (E.Abs _ levels _ exp) = VFun (map (\(B.ExpLevel (pat, _)) -> (B.Level pat , E.UnguardedRHS exp Nothing)) (filterTypesFromLevels levels))  
eval (_, local) (E.Abs _ levels _ exp) = VClosure (map (\(B.ExpLevel (pat, _)) -> pat) (filterTypesFromLevels levels)) exp local
eval _ (E.Let _ letDecl exp) = trace ("Let -> letDecl: " ++ show letDecl ++ " exp: " ++ show exp) undefined 
eval _ (E.Case _ exp pats) = trace ("Case -> exp: " ++ show exp ++ " pats: " ++ show pats) undefined
eval ctx (E.If _ ifExp thenExp elseExp) = if fstToHsBool (eval ctx ifExp) then eval ctx thenExp else eval ctx elseExp
eval _ (E.Channel _ type') = trace ("Channel -> type: " ++ show type') undefined
eval _ (E.Select _ iden) = trace ("Select -> iden: " ++ show iden) undefined

-- interpreter assumes that var fetches can't fail (checks were done before)
-- Might need to change to identify partial applied functions
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

-- Here is where the function application is done.
-- Because of how the parser parses function applications (f a b c d => f [a, b, c, d] even if f only takes one arg)
-- is necessary to repeat the evaluation until [arg] is empty.
-- TODO: context is a mess must check if it is correct, don't like that there is a lot of repetition
-- TODO: add suport for where clauses on functions
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
    if length pats == length args then case rhs of
      E.UnguardedRHS exp Nothing -> eval (global, matched) exp 
    -- TODO: implement when matched > args and when matched < args
    else if length pats < length args then case rhs of
      E.UnguardedRHS exp Nothing -> consumeAllArgs (global, matched) (eval (global, matched) exp) (drop (length pats) args)
    else case rhs of
      E.UnguardedRHS exp Nothing -> VClosure (drop (length args) pats) exp matched
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
-- Is there builtins that take no arguments?
consumeAllArgs ctx (VBuiltin builtin) [] = builtin VUnit
consumeAllArgs ctx (VBuiltin builtin) [arg] = builtin arg
consumeAllArgs ctx (VBuiltin builtin) (arg:args) = consumeAllArgs ctx (builtin arg) args
 
-- TODO: refactor to use map and filter?
doPatternMatching :: [E.Pat] -> [Value] -> [Maybe (String, Value)]
doPatternMatching [] [] = []
doPatternMatching pats [] = []
doPatternMatching [] args = []
-- TODO: finish implementing the rest of the patterns (ConsPat is partially implemented)
doPatternMatching (pat:pats) (arg:args) = case pat of
  E.WildPat _ _ -> doPatternMatching pats args
  E.VarPat _ var -> Just (B.external var, arg) : doPatternMatching pats args
  E.ConsPat _ (B.Identifier _ str) pats -> if (\(VCons str) -> str) arg == str then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.TuplePat _ _ -> undefined
  E.IntPat _ n -> if (\(VInt n) -> n) arg == n then doPatternMatching pats args else Nothing : doPatternMatching pats args 
  E.FloatPat _ n -> if (\(VFloat n) -> n) arg == float2Double n then doPatternMatching pats args else Nothing : doPatternMatching pats args 
  E.CharPat _ c -> if (\(VChar c) -> c) arg == c then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.StringPat _ str -> if (\(VString str) -> str) arg == str then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.AsPat _ var pat -> undefined

chooseRhs :: [([E.Pat], E.RHS)] -> [Value] -> Maybe (E.RHS, [(String, Value)], [E.Pat])
chooseRhs [] _ = Nothing
chooseRhs ((pats, rhs):rest) args = case sequence $ doPatternMatching pats args of
  Just matching -> Just (rhs, matching, pats)
  Nothing -> chooseRhs rest args
