{- |
Module      :  Syntax.Names
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains helper functions to generate variables with standard names.
-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Names where

import Syntax.Base
import qualified Syntax.Type as T

; mkOr, mkAnd,
  mkPlus, mkMinus, mkTimes, mkDiv, mkPower, mkNegate,
  mkPlusDot, mkMinusDot, mkTimesDot, mkDivDot, mkTimesTimes,
  mkDollar, mkRTriangle, mkSemi,
  mkPlusPlus, mkCaretCaret
  :: Located a => a -> Variable
mkOr = mkVar "(||)"
mkAnd = mkVar "(&&)"
mkPlus = mkVar "(+)"
mkMinus = mkVar "(-)"
mkTimes = mkVar "(*)"
mkDiv = mkVar "(/)"
mkPower = mkVar "(^)"
mkNegate = mkVar "negate"
mkPlusDot = mkVar "(+.)"
mkMinusDot = mkVar "(-.)"
mkTimesDot = mkVar "(*.)"
mkDivDot = mkVar "(/.)"
mkTimesTimes = mkVar "(**)"
mkDollar = mkVar "($)"
mkRTriangle = mkVar "(|>)"
mkSemi = mkVar "(;)"
mkPlusPlus = mkVar "(++)"
mkCaretCaret = mkVar "(^^)"

mkCmp :: Located a => String -> a -> Variable
mkCmp s = mkVar $ "("++s++")"

mkNil, mkCons :: Located a => a -> Identifier
mkNil  = mkId "[]"
mkCons = mkId "(::)"

mkTupleCons :: Located a => Int -> a -> Identifier
mkTupleCons n = mkId $ "("++replicate n ','++")"

mkBool :: Located a => a -> T.Type
mkBool (getSpan -> s) = T.Name s (mkId "Bool" s)