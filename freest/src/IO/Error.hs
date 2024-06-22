{- |
Module      :  IO.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress.
-}
module IO.Error 
  (Error(..))
where 

import Parser.Token
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T

import Data.List (intercalate)
import qualified Data.Map as Map

data Error 
  = LexicalError Span Char 
  | ParseError Span (Token, [String])
  | OutOfScope Span Variable
  | ConflictingDef (Map.Map String [Span])
  | MultipleVarDecls Span Variable
  | MultipleConsDecls Span Identifier
  | MultipleTypeDecls Span Identifier
  | UnexpectedTypeArg Span T.Type T.Type E.Exp
  | UnexpectedValueArg Span E.Exp K.Kind E.Exp
  | TooManyArgs Span E.Exp Int Int
  | LinVarsConsumedInUnFun Span [Variable] E.Exp
  | LinVarsCreatedInUnFun Span [Variable] E.Exp


instance Located Error where
  getSpan (LexicalError s _) = s
  getSpan (ParseError s _) = s
  getSpan (OutOfScope s _) = s
  getSpan (ConflictingDef xss) = foldr1 spanFromTo $ concat $ Map.elems xss
  getSpan (MultipleVarDecls s _) = s
  getSpan (MultipleConsDecls s _) = s
  getSpan (MultipleTypeDecls s _) = s
  getSpan (UnexpectedTypeArg s _ _ _) = s
  getSpan (UnexpectedValueArg s _ _ _) = s
  getSpan (TooManyArgs s _ _ _) = s
  getSpan (LinVarsConsumedInUnFun s _ _) = s
  getSpan (LinVarsCreatedInUnFun s _ _) = s

  setSpan = error "setSpan: span not settable"

instance Show Error where
  show e = show (getSpan e) ++ ": error:"++showError e
    where 
      showError (LexicalError _ inp) = 
        "\n  Lexical error on input "++show inp
      showError (ParseError _ (_,ss)) = 
        "\n  Parse error, expected: "++intercalate ", " ss
      showError (OutOfScope _ x) = 
        "\n  Variable not in scope: "++external x
      showError (ConflictingDef xss) = 
        "\n  Conflicting definitions in patterns:"
        ++Map.foldrWithKey 
          (\x ss msg -> 
            "\n    Variable '"++x++"' bound at:"
            ++foldr (\s msg' -> "\n      "++show s++msg') "" ss
            ++msg)
          "" xss
      showError (MultipleVarDecls _ c) =
        "\n  Multiple declarations of variable '"++show c++"'"
      showError (MultipleConsDecls _ c) =
        "\n  Multiple declarations of constructor '"++show c++"'"
      showError (MultipleTypeDecls _ c) =
        "\n  Multiple declarations of type '"++show c++"'"
      showError (UnexpectedTypeArg _ t1 t2 e2) =
        "\n  Expected a value argument of type '"++show t1++"' but got type argument '"++show t2++"' instead."
        ++"\n  In the expression:"++show e2
      showError (UnexpectedValueArg _ e1 k e2) =
        "\n  Expected a type argument of kind "++show k++" but got value argument '"++show e1++"' instead."
        ++"\n  In the expression:"++show e2
      showError (TooManyArgs _ f expected actual) =
        "\n  Expression "++show f++" takes "++show expected++" arguments, but it was given "++show actual
      showError (LinVarsConsumedInUnFun _ xs e) =
        "\n  Linear variables " ++ show xs ++ " consumed in the body of unrestricted function " ++ show e ++
        "\n  (This allows duplicating or discarding the variables! Consider using a linear function.)"
      showError (LinVarsCreatedInUnFun _ xs e) =
        "\n  Linear variables " ++ show xs ++ " consumed in the body of unrestricted function " ++ show e ++
        "\n  (This allows duplicating or discarding the variables! Consider using a linear function.)"