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
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T

import qualified Data.List.NonEmpty as NE

dummyKindVar :: Located a => a -> K.Kind
dummyKindVar (getSpan -> s) =
  K.Proper s (K.VarM  (Variable s "φ" (-1))) (K.VarPK (Variable s "ψ" (-1)))

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

tupleExp :: Span -> [E.Exp] -> E.Exp
tupleExp s es = E.App s (E.DCons s (mkTupleId (length es - 1) s)) (map ExpLevel es)

listExp :: Span -> T.Type -> [E.Exp] -> E.Exp
listExp s t = 
  foldr (\e l -> E.App s (E.DCons s $ mkConsId s) 
                         (TypeLevel t : map ExpLevel [e,l])) 
        (E.App s (E.DCons s (mkNilId s)) [TypeLevel t])

addArgExp :: Level E.Exp T.Type -> E.Exp -> E.Exp 
addArgExp a (E.App s e as) = E.App s e (as ++ [a])
addArgExp a e              = E.App (spanFromTo e a) e [a]

addArgType :: T.Type -> T.Type -> T.Type
addArgType t (T.App s u us)   = T.App s u (us ++ [t])
addArgType t u                = T.App (spanFromTo u t) u [t]
