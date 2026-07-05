{- |
Module      :  Syntax.Provenance
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Provenance for inference constraints.
-}
module Syntax.Provenance
  ( Origin(..)
  )
where

import Syntax.Base ( Span, Located(..) )

-- | Where an inference constraint arose. Just a span (for now...)
newtype Origin = Origin Span

instance Located Origin where
  getSpan (Origin s)   = s
  setSpan s (Origin _) = Origin s
