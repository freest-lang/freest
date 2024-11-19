{- |
Module      :  UI.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress.
-}
{-# LANGUAGE LambdaCase #-}
module UI.Error 
  (Error(..))
where 

import Parser.Token
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T
import Utils

import Data.List (intercalate)
import qualified Data.Map.Strict as Map

data Error 
  = LexicalError Span Char 
  | ParseError Span (Token, [String])
  | OutOfScope Span Variable
  | TypeOutOfScope Span Identifier
  | ConflictingDefs (Map.Map (Level String String) [Span])
  | MultipleVarDecls Span Variable
  | MultipleConsDecls Span Identifier
  | MultipleTypeDecls Span Identifier
  | TooManyArgs Span E.Exp T.Type Int Int
  | LinVarsConsumedInUnFun Span [Variable] E.Exp
  | LinVarsCreatedInUnFun Span [Variable] E.Exp
  | ExposeError Span String (Either E.Pat E.Exp) T.Type
  | UnexpectedArg Span (Level T.Type K.Kind) (Level E.Exp T.Type) Int E.Exp
  | NonLinPat Span E.Pat T.Type
  | KindMismatch Span K.Kind T.Type K.Kind
  | TooManyArgsK Span T.Type K.Kind Int Int
  | InvalidType Span T.Type


instance Located Error where
  getSpan (LexicalError s _) = s
  getSpan (ParseError s _) = s
  getSpan (OutOfScope s _) = s
  getSpan (TypeOutOfScope s _) = s
  getSpan (ConflictingDefs xss) = foldr1 spanFromTo $ concat $ Map.elems xss
  getSpan (MultipleVarDecls s _) = s
  getSpan (MultipleConsDecls s _) = s
  getSpan (MultipleTypeDecls s _) = s
  getSpan (TooManyArgs s _ _ _ _) = s
  getSpan (LinVarsConsumedInUnFun s _ _) = s
  getSpan (LinVarsCreatedInUnFun s _ _) = s
  getSpan (ExposeError s _ _ _) = s
  getSpan (UnexpectedArg s _ _ _ _) = s
  getSpan (NonLinPat s _ _) = s
  getSpan (KindMismatch s _ _ _) = s
  getSpan (TooManyArgsK s _ _ _ _) = s
  getSpan (InvalidType s _) = s

  setSpan = internalError "span not settable for Error type."

instance Show Error where
  show e = show (getSpan e) ++ ": error:"++showError e
    where 
      showError :: Error -> String
      showError = \case
        LexicalError _ inp ->
          "\n  Lexical error on input `"++show inp++"`"
        ParseError _ (_,ss) -> 
          "\n  Parse error, expected: `"++intercalate "`, `" ss++"`"
        OutOfScope _ x -> 
          "\n  Not in scope: variable `"++external x++"`"
        TypeOutOfScope _ i ->
          "\n Not in scope: type constructor `"++show i++"`"
        ConflictingDefs vos -> 
          "\n  Conflicting definitions in patterns:"
          ++Map.foldrWithKey (\case 
              ExpLevel x -> \ss msg -> 
                  "\n    Variable `"++x++"` bound at:"
                  ++foldr (\s msg' -> "\n      "++show s++msg') "" ss
                  ++msg
              TypeLevel a -> \ss msg -> 
                  "\n    Type variable `"++a++"` bound at:"
                  ++foldr (\s msg' -> "\n      "++show s++msg') "" ss
                  ++msg)
          "" vos
        MultipleVarDecls _ c ->
          "\n  Multiple declarations of variable `"++show c++"`"
        MultipleConsDecls _ c ->
          "\n  Multiple declarations of constructor `"++show c++"`"
        MultipleTypeDecls _ c ->
          "\n  Multiple declarations of type `"++show c++"`"
        TooManyArgs _ f t expected actual ->
          "\n  Expression `"++show f++"` of type `"++show t++"` takes "++show expected++" arguments, but it was given "++show actual++"."
        LinVarsConsumedInUnFun _ xs e ->
          "\n  Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in the body of unrestricted function `" ++ show e ++"`"++
          "\n  (This allows duplicating or discarding the variables! Consider using a linear function instead.)"
        LinVarsCreatedInUnFun _ xs e ->
          "\n  Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in the body of unrestricted function `" ++ show e ++"`"++
          "\n  (This allows duplicating or discarding the variables! Consider using a linear function instead.)"
        ExposeError _ s e t -> 
          "\n  Expecting "++s++" type for "++showExpPat e++", but got type `"++show t++"`"
            where showExpPat (Left  p) = "pattern `"++show p++"`"
                  showExpPat (Right e) = "expression `"++show e++"`"
        UnexpectedArg _ (TypeLevel k) (ExpLevel e) n f -> 
          "\n  Expecting a type argument of kind `"++show k++"`, but got value argument `"++show e++"` instead."++
          "\n  In the "++show n {- TODO: use numerals-}++"th argument of function `"++show f++"`."
        UnexpectedArg _ (ExpLevel  t) (TypeLevel u) n f -> 
          "\n  Expecting a value argument of type `"++show t++"`, but got type argument `"++show u++"` instead."++
          "\n  In the "++show n {- TODO: use numerals-}++"th argument of function `"++show f++"`."
        NonLinPat s p t ->
          "\n  Non-linear pattern `"++show p++"` on linear type `"++show t++"`." -- TODO: better error
        KindMismatch s k1 t k2 ->
          "\n Expected kind "++show k1++" for type "++show t++", but got kind "++show k2
        TooManyArgsK s t k n m ->
          "\n Type "++show t++" : "++show k++" expects "++show n++" arguments, but it was given "++show m++"."
        InvalidType s t ->
          "\n Invalid type: "++show t
