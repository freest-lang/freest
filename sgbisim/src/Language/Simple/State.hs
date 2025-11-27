{- |
Module      :  Bisimulation.State
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module TODO
-}

module Language.Simple.State
  ( Norm(..)
  , NormTable
  , Bisimulation
  , BisimulationState (..)
  , Basis
  , Bpa (..)
  , Node (..)
  , Queue
  , Branch
  , putBasis
  , modifyBasis
  , lookupBasis
  , modifyNormTable
  , putVisitedPairs
  , modifyVisitedPairs
  )
where

import Language.Simple.Grammar

import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Prelude hiding ( Word, log )

-- Table to store the norm of each non-terminal
type NormTable = Map.Map Nonterminal Norm

-- isBisimilar types
data Node = Node
  { pair   :: (Word, Word)                                                     
  , parent :: Maybe Node
  } 
  deriving (Show, Eq)

type Branch = Node

type Queue = Seq.Seq Branch

type Basis = Map.Map (Nonterminal, Nonterminal) Bpa

data Bpa = Bpa1 Word | Bpa2 (Word, Word)

instance Show Bpa where
  show (Bpa1 n) = show n
  show (Bpa2 (n, m)) = show (n, m)

type Bisimulation = State BisimulationState

data BisimulationState = BisimulationState
  { basis :: Basis
  , visitedPairs :: Set.Set (Word, Word)
  , normTable :: NormTable
  , productions :: Productions
  }

putVisitedPairs :: Set.Set (Word, Word) -> Bisimulation ()
putVisitedPairs = modifyVisitedPairs . const

modifyVisitedPairs :: (Set.Set (Word, Word) -> Set.Set (Word, Word)) -> Bisimulation ()
modifyVisitedPairs f = 
  modify \s -> s{visitedPairs = f (visitedPairs s)}

putBasis :: Basis -> Bisimulation ()
putBasis = modifyBasis . const

modifyBasis :: (Basis -> Basis) -> Bisimulation ()
modifyBasis f = modify \s -> s{basis = f (basis s)}

lookupBasis :: (Nonterminal, Nonterminal) -> Bisimulation (Maybe Bpa)
lookupBasis (x, y) | x == y    = return (Just (Bpa1 []))
                   | otherwise = gets (Map.lookup (x,y) . basis)

modifyNormTable :: (NormTable -> NormTable) -> Bisimulation ()
modifyNormTable f = modify \s -> s{normTable = f (normTable s)}
