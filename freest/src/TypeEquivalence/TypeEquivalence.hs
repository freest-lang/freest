{- |
Module      :  TypeEquivalence.TypeEquivalence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Check whether two types are equivalent, by first testing whether they are
alpha-congruent and, if not, whether they are bisimilar.
-}

module TypeEquivalence.TypeEquivalence
  ( equivalent
  )
where

import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           SimpleGrammar.FromType        ( fromType )
-- import qualified Bisimulation.Bisimulation     ( bisimilar )

equivalent :: TypeDeclMap -> T.Type -> T.Type -> Bool
equivalent td t u = t == u || bisimilar td t u

bisimilar :: TypeDeclMap -> T.Type -> T.Type -> Bool
bisimilar td t u = let _ = fromType td [t, u] in True
-- bisimilar td t u = bisimilar $ fromType td [t, u]

-- TODO: Move this code to module Bisimulation.Bisimulation
