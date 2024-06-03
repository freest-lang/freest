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
import Parser.Token

import Data.List (intercalate)

data Error 
  = LexicalError Span Char 
  | ParseError Span (Token, [String])
  | OutOfScope Span Variable

instance Located Error where
  getSpan (LexicalError s _) = s
  getSpan (ParseError s _) = s
  getSpan (OutOfScope s _) = s
  setSpan s (LexicalError _ c) = LexicalError s c
  setSpan s (ParseError _ tk) = ParseError s tk
  setSpan s (OutOfScope _ x) = OutOfScope s x

instance Show Error where
  show e = show (getSpan e) ++ ": error:\n\t"++showError e
    where showError (LexicalError _ inp) = "Lexical error on input "++show inp
          showError (ParseError _ (_,ss)) = "Parse error, expected: "++intercalate ", " ss
          showError (OutOfScope _ x) = "Variable not in scope: "++external x
