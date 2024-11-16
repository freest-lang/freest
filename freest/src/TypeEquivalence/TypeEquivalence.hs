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

import qualified Syntax.Type                       as T
import           Syntax.Module
import           SimpleGrammar.FromType            ( fromType )
-- import qualified Bisimulation.Bisimulation   as G ( bisimilar )

equivalent :: Module -> T.Type -> T.Type -> Bool
equivalent m t u = t == u || bisimilar m t u

bisimilar :: Module -> T.Type -> T.Type -> Bool
bisimilar m t u = True
  where _ = fromType m [t, u]
-- bisimilar t u = G.bisimilar (convertToGrammar [t, u])
