{- |
Module      :  TypeEquivalence.TypeEquivalence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Check whether two types are equivalent, by first testing whether they are
alpha-congruent and, if not, whether they are bisimilar.
-}

module Validation.TypeEquivalence.TypeEquivalence
  ( equivalent
  )
where

import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.TypeEquivalence.FromType ( fromType )
import Language.Simple.Bisimulation ( bisimilar )

equivalent :: TypeDeclMap -> T.Type -> T.Type -> Bool
equivalent td t u =
  t == u ||
  bisimilar (fromType td [t, u])

-- TODO: Move this code to module Bisimulation.Bisimulation
