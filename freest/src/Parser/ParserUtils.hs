{- |
Module      :  Parser.ParserUtils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains utilities for parsing, namely for generating fresh variables
and constructing types and expressions more succinctly.
-}
{-# LANGUAGE ViewPatterns #-}
module Parser.ParserUtils where

import Parser.Token
import Parser.LexerUtils
import Syntax.Base
import Syntax.Names
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Type qualified as T

import Data.List.NonEmpty qualified as NE

dummyKindVar :: Located a => a -> K.Kind
dummyKindVar (getSpan -> s) =
  K.Var s (Variable s "τ" defaultInternal)

split :: Eq a => a -> [a] -> [[a]]
split d str =
  case break (==d) str of
    (a, _:b) -> a : split d b
    (a, _)   -> [a]

mkVarTk :: Token -> Variable
mkVarTk t = mkDefaultVar (getText t) t

mkIdTk :: Token -> Identifier
mkIdTk t = mkId (getText t) t

infixApp :: T.Type -> T.Type -> T.Type -> T.Type
infixApp t1 op t2 = T.App (spanFromTo t1 t2) op [t1, t2]

binOp :: E.Exp -> E.Exp -> E.Exp -> E.Exp
binOp l op r = E.App (spanFromTo l r) op [ExpLevel l, ExpLevel r]

unOp :: E.Exp -> E.Exp -> E.Exp
unOp op x = E.App (spanFromTo op x) op [ExpLevel x]

addArgExp :: Level E.Exp T.Type -> E.Exp -> E.Exp
addArgExp a (E.App s e as) = E.App s e (as ++ [a])
addArgExp a e              = E.App (spanFromTo e a) e [a]

addArgType :: T.Type -> T.Type -> T.Type
addArgType t u@T.AppLinChoice{} = T.App (spanFromTo u t) u [t]
addArgType t u@T.AppSemi{}      = T.App (spanFromTo u t) u [t]
addArgType t u@T.AppDual{}      = T.App (spanFromTo u t) u [t]
addArgType t u@T.AppQuant{}     = T.App (spanFromTo u t) u [t]
addArgType t (T.App s u us)     = T.App s u (us ++ [t])
addArgType t u                  = T.App (spanFromTo u t) u [t]
