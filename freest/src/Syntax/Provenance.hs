{- |
Module      :  Syntax.Provenance
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Provenance for inference constraints.
-}
module Syntax.Provenance
  ( Origin(..)
  , Reason(..)
  )
where

import Syntax.Base ( Span, Located(..) )

-- | Why and where a constraint arose.
data Origin = Origin Span Reason

-- | The source construct a constraint originates from.
data Reason
  = FromArrow
  | FromForall
  | FromKind
  | FromLambda
  | FromInferred
  | Derived Origin

instance Located Origin where
  getSpan (Origin s _)   = s
  setSpan s (Origin _ r) = Origin s r
