{- |
Module      :  Syntax.Names
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains helper functions to generate variables with standard names.
-}
module Syntax.Names where

import Syntax.Base

mk :: Located a => String -> a -> Variable
mk = flip mkVar

; mkOr, mkAnd,
  mkPlus, mkMinus, mkTimes, mkDiv, mkPower, mkNegate,
  mkPlusDot, mkMinusDot, mkTimesDot, mkDivDot, mkTimesTimes,
  mkDollar, mkRTriangle, mkSemi,
  mkPlusPlus, mkCaretCaret,
  mkCons, mkNil,
  mkSelect 
  :: Located a => a -> Variable
mkOr = mk "(||)"
mkAnd = mk "(&&)"
mkPlus = mk "(+)"
mkMinus = mk "(-)"
mkTimes = mk "(*)"
mkDiv = mk "(/)"
mkPower = mk "(^)"
mkNegate = mk "negate"
mkPlusDot = mk "(+.)"
mkMinusDot = mk "(-.)"
mkTimesDot = mk "(*.)"
mkDivDot = mk "(/.)"
mkTimesTimes = mk "(**)"
mkDollar = mk "($)"
mkRTriangle = mk "(|>)"
mkSemi = mk "(;)"
mkPlusPlus = mk "(++)"
mkCaretCaret = mk "(^^)"
mkCons = mk "(::)"
mkNil  = mk "[]"
mkSelect = mk "select"

mkCmp :: Located a => String -> a -> Variable
mkCmp s = mk $ "("++s++")"

mkTupleCons :: Located a => Int -> a -> Variable
mkTupleCons n = mk $ "("++replicate n ','++")"

