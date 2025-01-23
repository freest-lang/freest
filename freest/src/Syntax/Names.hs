{- |
Module      :  Syntax.Names
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains helper functions to generate variables with standard names.
-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Names where

import Syntax.Base

; mkOr, mkAnd,
  mkPlus, mkMinus, mkTimes, mkDiv, mkPower, mkNegate,
  mkPlusDot, mkMinusDot, mkTimesDot, mkDivDot, mkTimesTimes,
  mkDollar, mkRTriangle, mkSemi,
  mkPlusPlus, mkCaretCaret
  :: Located a => a -> Variable
mkOr = mkDefaultVar "(||)"
mkAnd = mkDefaultVar "(&&)"
mkPlus = mkDefaultVar "(+)"
mkMinus = mkDefaultVar "(-)"
mkTimes = mkDefaultVar "(*)"
mkDiv = mkDefaultVar "(/)"
mkPower = mkDefaultVar "(^)"
mkNegate = mkDefaultVar "negate"
mkPlusDot = mkDefaultVar "(+.)"
mkMinusDot = mkDefaultVar "(-.)"
mkTimesDot = mkDefaultVar "(*.)"
mkDivDot = mkDefaultVar "(/.)"
mkTimesTimes = mkDefaultVar "(**)"
mkDollar = mkDefaultVar "($)"
mkRTriangle = mkDefaultVar "(|>)"
mkSemi = mkDefaultVar "(;)"
mkPlusPlus = mkDefaultVar "(++)"
mkCaretCaret = mkDefaultVar "(^^)"

mkCmp :: Located a => String -> a -> Variable
mkCmp s = mkDefaultVar $ "("++s++")"

mkUnit, mkNil, mkCons :: Located a => a -> Identifier
mkUnit = mkId "()"
mkNil  = mkId "[]"
mkCons = mkId "(::)"

mkTupleCons :: Located a => Int -> a -> Identifier
mkTupleCons n = mkId $ "("++replicate n ','++")"

mkBool :: Located a => a -> Identifier
mkBool (getSpan -> s) = mkId "Bool" s

mkList :: Located a => a -> Identifier
mkList (getSpan -> s) = mkId "[]" s
