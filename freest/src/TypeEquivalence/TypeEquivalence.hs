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
import           TypeEquivalence.AlphaCongruence
-- import           SimpleGrammar.TypeToGrammar ( convertToGrammar )
-- import qualified Bisimulation.Bisimulation   as G ( bisimilar )

equivalent :: T.Type -> T.Type -> Bool
equivalent t u = t `alphaCongruent` u || t `bisimilar` u

bisimilar :: T.Type -> T.Type -> Bool
bisimilar t u = True
-- bisimilar t u = G.bisimilar (convertToGrammar [t, u])
