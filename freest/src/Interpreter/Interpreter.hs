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

-- is this the best way to do this?
data Value = VInt Int
            | VFloat Double
            | VUnit 
            | VChar Char
            | VString String
            | VTuple [Value]
            | VFun [([E.Pat], E.RHS)]
            | VAbs [E.Pat] E.Exp
            deriving Show

-- Using a simple context for now for simplicity
-- Should context be of this type or the Value should be an Expression (FreeST is eagerly evalliated so it should be ok)
type Context = [(B.Variable, Value)]

-- Maybe module is not needed if information is put on the context
interpret :: M.Module -> Either [IOE.Error] Value
interpret m = case getMainFunction m of
  -- Assuming that the RHS of main is always in the form main = <exp>
  -- necessary to initialize the context with information from the module
  -- other modules, prelude, etc
  Just (E.ValDecl _ (E.UnguardedRHS mainExp _)) -> Right $ eval m [(initContext m)] mainExp
  -- Return unit when main function is not present
  Nothing -> Right VUnit

getMainFunction :: M.Module -> Maybe LetDecl 
getMainFunction m = find foo (M.definitions m)
  -- main should be a ValDecl VarPat because it is the form main = <body>
  where foo funDef = case funDef of E.ValDecl (E.VarPat _ var) _ -> B.external var == "main"  
                                    _ -> False

-- For now add to the context definitions. Only later will be added imports  
initContext :: M.Module -> Context
initContext m =
  -- is VarPat the only valid pattern in a valDecl??
  -- the same for the rhs UnguardedRHS
  map (\def -> case def of E.ValDecl (E.VarPat _ var) (E.UnguardedRHS exp _) -> (var, eval m [] exp)
                           -- E.FnDecl var (((B.ExpLevel pat):pats, rhs):levels) -> trace ("FnDecl -> " ++ "var: " ++ (show var) ++ " pat: " ++ (show pat) ++ " pats: " ++ (show pats) ++ " rhs: " ++ (show rhs) ++ " levels: " ++ (show levels)) undefined
                           E.FnDecl var fun -> (var, VFun (map (\(levels, rhs) -> ((map (\(B.ExpLevel pat) -> pat) levels), rhs)) fun))
  -- do not add main to the context
  ) (filter (\def -> case def of E.ValDecl (E.VarPat _ var) _ -> B.external var /= "main" 
                                 E.SigDecl _ _ -> False
                                 _ -> True)
    (M.definitions m))

eval :: M.Module -> [Context] -> E.Exp -> Value
eval _ _ (E.Int _ n) = VInt n 
eval _ _ (E.Float _ n) = VFloat n
eval _ _ (E.Char _ c) = VChar c
eval _ _ (E.String _ str) = VString str
-- [Exp] -> [Value]
eval m ctxs (E.Tuple _ tup) = VTuple (map (eval m ctxs) tup)
-- the hell is this Cons
-- for now i return unit
eval _ _ (E.Cons _ (B.Identifier _ str)) = trace ("E.Cons is " ++ show str) VUnit
eval _ (ctx:ctxs) (E.Var _ var) = getVar ctx var
-- look for the function in exp (should be a variable or an lambda abstraction)
-- do arguments substituion
-- returns the result of the computation
-- or another lambda abstraction if there is still free variables?? Currying?!
eval _ ctxs (E.App _ exp level) = trace ("App -> exp: " ++ (show exp) ++ " level: " ++ (show level) ++ " | Ctxs: " ++ (show ctxs)) VUnit
-- assuming that the Pat is always WildPat (why is that and not VarPat)
-- eval _ _ (E.Abs _ levels _ exp) = VFun (map (\(B.ExpLevel (pat, _)) -> (B.Level pat , E.UnguardedRHS exp Nothing)) levels)  
eval _ _ (E.Abs _ levels _ exp) = VAbs (map (\(B.ExpLevel (pat, _)) -> pat) levels) exp
eval _ _ (E.Let _ letDecl exp) = trace ("Let -> letDecl: " ++ (show letDecl) ++ " exp: " ++ (show exp)) undefined 
eval _ _ (E.Case _ exp pats) = trace ("Case -> exp: " ++ (show exp) ++ " pats: " ++ (show pats)) undefined
eval m ctxs (E.If _ ifExp thenExp elseExp) = if isTrue (eval m ctxs ifExp) then (eval m ctxs thenExp) else (eval m ctxs elseExp)
eval _ _ (E.Channel _ type') = trace ("Channel -> type: " ++ (show type')) undefined
eval _ _ (E.Select _ iden) = trace ("Select -> iden: " ++ (show iden)) undefined

-- interpreter assumes that var fetches can't fail (checks were done before)
getVar :: Context -> B.Variable -> Value
getVar ctx var = case find (\(var2, val) -> var == var2) ctx of
  Just (var, val) -> val
  -- maybe use Either monad here
  Nothing -> error "Variable not found in the context. This should not happen. This is a bug in the compiler"

-- check if expression is true
isTrue :: Value -> Bool
isTrue exp = undefined
