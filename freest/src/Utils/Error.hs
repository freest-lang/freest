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
  | MultipleDecls Span Variable

instance Located Error where
  getSpan (LexicalError s _) = s
  getSpan (ParseError s _) = s
  getSpan (OutOfScope s _) = s
  getSpan (ConflictingDef vos) = foldr1 spanFromTo $ concat $ Map.elems vos
  getSpan (MultipleDecls s _) = s

  setSpan = error "setSpan: span not settable"

instance Show Error where
  show e = show (getSpan e) ++ ": error:\n\t"++showError e
    where 
      showError (LexicalError _ inp) = 
        "Lexical error on input "++show inp
      showError (ParseError _ (_,ss)) = 
        "Parse error, expected: "++intercalate ", " ss
      showError (OutOfScope _ x) = 
        "Variable not in scope: "++external x
      showError (ConflictingDef vos) = 
        "Conflicting definitions in pattern:"
        ++Map.foldrWithKey 
          (\x ss msg -> 
            "\n\tVariable '"++x++"' bound at:"
            ++foldr (\s msg' -> "\n\t\t"++show s++msg') "" ss
            ++msg)
          "" vos
      showError (MultipleDecls _ c) =
        "Multiple declarations of '"++external c++"'"
