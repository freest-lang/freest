{- |
Module      :  TypeEquivalence.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module TODO
-}

module TypeEquivalence.Rename
 ( rename
 )
where

import           Syntax.Base
import qualified Syntax.Type                   as T

import qualified Data.Set                      as Set

-- TODO: complete me!
rename :: T.Type -> T.Type
rename = ren Set.empty
  where
    ren :: Set.Set Int -> T.Type -> T.Type
    ren _ = id

first :: Set.Set Int -> Variable
first s = Variable nullSpan ('#' : show n) n
  where n = head $ filter (`Set.notMember` s) [0..]

