{- |
Module      :  Utils.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress.
-}
module Utils.Error 
  (Error(..))
where 

import Syntax.Base
import qualified Syntax.Expression as E
import Parser.Token

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

instance Located Error where
  getSpan (LexicalError s _) = s
  getSpan (ParseError s _) = s
  getSpan (OutOfScope s _) = s
  getSpan (ConflictingDef xss) = foldr1 spanFromTo $ concat $ Map.elems xss
  getSpan (MultipleVarDecls s _) = s
  getSpan (MultipleConsDecls s _) = s
  getSpan (MultipleTypeDecls s _) = s

  setSpan = error "setSpan: span not settable"

instance Show Error where
  show e = show (getSpan e) ++ ": error:\n  "++showError e
    where 
      showError (LexicalError _ inp) = 
        "Lexical error on input "++show inp
      showError (ParseError _ (_,ss)) = 
        "Parse error, expected: "++intercalate ", " ss
      showError (OutOfScope _ x) = 
        "Variable not in scope: "++external x
      showError (ConflictingDef xss) = 
        "Conflicting definitions in patterns:"
        ++Map.foldrWithKey 
          (\x ss msg -> 
            "\n    Variable '"++x++"' bound at:"
            ++foldr (\s msg' -> "\n      "++show s++msg') "" ss
            ++msg)
          "" xss
      showError (MultipleVarDecls _ c) =
        "Multiple declarations of variable '"++show c++"'"
      showError (MultipleConsDecls _ c) =
        "Multiple declarations of constructor '"++show c++"'"
      showError (MultipleTypeDecls _ c) =
        "Multiple declarations of type '"++show c++"'"
