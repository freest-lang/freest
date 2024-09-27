module Interpreter.Interpreter where

import Data.List ( find )
-- for debuging don't forget to remove
import Debug.Trace

import qualified Syntax.Module as M
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import Syntax.Expression ( LetDecl )
import IO.Error as IOE

type Value = Int

interpret :: M.Module -> Either [IOE.Error] Value
interpret m = case getMainFunction m of
  -- Assuming that the RHS of main is always in the form main = <exp>
  Just (E.ValDecl _ (E.UnguardedRHS mainExp _)) -> Right $ eval m mainExp
  -- Return unit when main function is not present
  Nothing -> Right 0

getMainFunction :: M.Module -> Maybe LetDecl 
getMainFunction m = find foo (M.definitions m)
                                    -- main should be a ValDecl VarPat because it is the form main = <body>
  where foo funDef = case funDef of E.ValDecl (E.VarPat _ var) _ -> B.external var == "main"  
                                    _ -> False

eval :: M.Module -> E.Exp -> Value
eval _ e = trace (show e) undefined
