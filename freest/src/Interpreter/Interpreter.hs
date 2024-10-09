module Interpreter.Interpreter where

import Data.List ( find )
-- for debuging don't forget to remove
import Debug.Trace
-- ends here

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
            | VTuple [Value]
            | VFun [([E.Pat], E.RHS)]
            -- do closures capture only the local ctx or also the global?
            | VClosure [E.Pat] E.Exp (Context, Context)
            deriving Show

-- Using a simple context for now for simplicity
type Context = [(B.Variable, Value)]

interpret :: M.Module -> Either [IOE.Error] Value
interpret m = case getMainFunction (trace (show m) m) of
  -- Assuming that the RHS of main is always in the form main = <exp>
  -- necessary to initialize the context with information from the module
  -- other modules, prelude, etc
  Just (E.ValDecl _ (E.UnguardedRHS mainExp _)) -> Right $ eval ((initContext m), []) mainExp
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
  map (\def -> case def of E.ValDecl (E.VarPat _ var) (E.UnguardedRHS exp _) -> (var, eval ([], []) exp)
                           E.FnDecl var fun -> (var, VFun (map (\(levels, rhs) -> ((map (\(B.ExpLevel pat) -> pat) levels), rhs)) fun))
  -- do not add main to the context
  ) (filter (\def -> case def of E.ValDecl (E.VarPat _ var) _ -> B.external var /= "main" 
                                 E.SigDecl _ _ -> False
                                 _ -> True)
    (M.definitions m))

-- Global and local context
eval :: (Context, Context) -> E.Exp -> Value
eval _ (E.Int _ n) = VInt n 
eval _ (E.Float _ n) = VFloat n
eval _ (E.Char _ c) = VChar c
eval _ (E.String _ str) = VString str
-- [Exp] -> [Value]
eval ctx (E.Tuple _ tup) = VTuple (map (eval ctx) tup)
-- for now i return unit
eval _ (E.Cons _ (B.Identifier _ str)) = trace ("E.Cons is " ++ show str) VUnit
eval ctx (E.Var _ var) = getVar ctx var
eval ctx (E.App _ exp level) = 
  trace ("App -> exp: " ++ (show exp) ++ " level: " ++ (show level) ++ " | Ctx: " ++ (show ctx)) undefined
  -- let left = eval ctx exp in trace (show left) VUnit
-- eval _ _ (E.Abs _ levels _ exp) = VFun (map (\(B.ExpLevel (pat, _)) -> (B.Level pat , E.UnguardedRHS exp Nothing)) levels)  
eval ctx (E.Abs _ levels _ exp) = VClosure (map (\(B.ExpLevel (pat, _)) -> pat) levels) exp ctx
eval _ (E.Let _ letDecl exp) = trace ("Let -> letDecl: " ++ (show letDecl) ++ " exp: " ++ (show exp)) undefined 
eval _ (E.Case _ exp pats) = trace ("Case -> exp: " ++ (show exp) ++ " pats: " ++ (show pats)) undefined
eval ctx (E.If _ ifExp thenExp elseExp) = if isTrue (eval ctx ifExp) then (eval ctx thenExp) else (eval ctx elseExp)
eval _ (E.Channel _ type') = trace ("Channel -> type: " ++ (show type')) undefined
eval _ (E.Select _ iden) = trace ("Select -> iden: " ++ (show iden)) undefined

-- interpreter assumes that var fetches can't fail (checks were done before)
-- Might need to change to identify partial applied functions
-- Eww ungly, find better way of doing this (>>= but the opposite?)
getVar :: (Context, Context) -> B.Variable -> Value
getVar (global, local) var = case find (\(var2, val) -> B.external var == B.external var2) local of
  Just (var, val) -> val
  Nothing -> case find (\(var2, val) -> B.external var == B.external var2) local of
    Just (var, val) -> val
    Nothing -> error ("Variable `" ++ (show var) ++ "`not found in the context. This should not happen. This is a bug in the compiler")

-- check if expression is true (inside FreeST)
isTrue :: Value -> Bool
isTrue exp = undefined
