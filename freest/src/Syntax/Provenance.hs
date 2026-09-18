{- |
Module      :  Syntax.Provenance
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Provenance for inference constraints.
-}
module Syntax.Provenance
  ( Origin(..)
  , Reason(..)
  , explains
  )
where

import Syntax.Base ( Span, Located(..) )

-- | Where an inference constraint arose, and what kind of site that was. The
-- reason is what error messages blame: a constraint fixing a multiplicity at a
-- use or an application explains the requirement, whereas one read off a
-- written signature merely restates it.
data Origin = Origin Reason Span

-- | The kind of site a constraint arose at, most explanatory first.
data Reason = AtUse | AtApp | AtLambda | InSignature
  deriving (Eq, Ord, Enum, Bounded)

-- | How good an explanation a constraint from this origin is for a multiplicity
-- that was fixed unrestricted (or not), lower is better. A use only ever bounds
-- a multiplicity above by @*@, so it explains nothing about a linear one.
explains :: Bool -> Origin -> Int
explains un (Origin r _)
  | AtUse <- r, not un = maxBound
  | otherwise          = fromEnum r

instance Located Origin where
  getSpan (Origin _ s)   = s
  setSpan s (Origin r _) = Origin r s
