{- |
Module      :  Syntax.Names
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains helper functions to generate variables with standard names.
-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Names where

import Syntax.Base

; mkOrVar, mkAndVar,
  mkPlusVar, mkMinusVar, mkTimesVar, mkDivVar, mkPowerVar, mkNegateVar,
  mkPlusDotVar, mkMinusDotVar, mkTimesDotVar, mkDivDotVar, mkTimesTimesVar, mkNegateFVar,
  mkDollarVar, mkRTriangleVar, mkSemiVar, mkDotVar,
  mkPlusPlusVar, mkCaretCaretVar,
  mkSend, mkReceive, mkFork,
  mkUndefinedVar
  :: Located a => a -> Variable
mkOrVar = mkDefaultVar "(||)"
mkAndVar = mkDefaultVar "(&&)"
mkPlusVar = mkDefaultVar "(+)"
mkMinusVar = mkDefaultVar "(-)"
mkTimesVar = mkDefaultVar "(*)"
mkDivVar = mkDefaultVar "(/)"
mkPowerVar = mkDefaultVar "(^)"
mkNegateVar = mkDefaultVar "negate"
mkPlusDotVar = mkDefaultVar "(+.)"
mkMinusDotVar = mkDefaultVar "(-.)"
mkTimesDotVar = mkDefaultVar "(*.)"
mkDivDotVar = mkDefaultVar "(/.)"
mkTimesTimesVar = mkDefaultVar "(**)"
mkNegateFVar = mkDefaultVar "negateF"
mkDollarVar = mkDefaultVar "($)"
mkRTriangleVar = mkDefaultVar "(|>)"
mkSemiVar = mkDefaultVar "(;)"
mkDotVar = mkDefaultVar "(.)"
mkPlusPlusVar = mkDefaultVar "(++)"
mkCaretCaretVar = mkDefaultVar "(^^)"
mkSend = mkDefaultVar "send"
mkReceive = mkDefaultVar "receive"
mkFork = mkDefaultVar "fork"
mkUndefinedVar = mkDefaultVar "undefined"

mkCmpVar :: Located a => String -> a -> Variable
mkCmpVar s = mkDefaultVar $ "("++s++")"

mkUnitId, mkNilId, mkConsId :: Located a => a -> Identifier
mkUnitId = mkId "()"
mkNilId  = mkId "[]"
mkConsId = mkId "(::)"

mkTupleId :: Located a => Int -> a -> Identifier
mkTupleId n = mkId $ "("++replicate n ','++")"

isTupleId :: Identifier -> Bool
isTupleId (Identifier s ('(':cs)) = isTupleId' cs
  where
    isTupleId' = \case 
      (',':cs) -> isTupleId' cs
      ")"      -> True
      _        -> False
isTupleId _ = False

mkBoolId :: Located a => a -> Identifier
mkBoolId (getSpan -> s) = mkId "Bool" s

mkListId :: Located a => a -> Identifier
mkListId (getSpan -> s) = mkId "[]" s
