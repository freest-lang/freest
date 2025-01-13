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

import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.TypeEquivalence.FromType ( fromType )
import           Validation.TypeEquivalence.Bisimulation.Bisimulation ( bisimilar )
import           Debug.Trace                   (trace)

equivalent :: TypeDeclMap -> T.Type -> T.Type -> Bool
equivalent td t u =
  t == u ||
  -- trace ("\nThe types: " ++ show [t, u] ++ "\nand the grammar: " ++ show (fromType td [t, u])) True
  bisimilar (fromType td [t, u])


-- TODO: Move this code to module Bisimulation.Bisimulation
