{- |
Module      :  Bisimulation.State
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module TODO
-}

module Validation.TypeEquivalence.Bisimulation.State
  ( IOF
  , NormMap
  , GlobalState
  , GlobalStateData (..)
  , Basis
  , Bpa (..)
  , Node (..)
  , BranchQueue (..)
  , Branch
  , addLog
  , updateNormMap
  , replaceBasis
  , replaceVisitedPairs
  )
where

import Syntax.Base
import Validation.TypeEquivalence.Grammar

import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Prelude hiding ( Word, log )

-- Type used in norm
type IOF = Maybe Int

-- Map to store the norm of each nonTerminal
type NormMap = Map.Map NonTerminal IOF

-- isBisimilar types
data Node = Node
  { nodeValue :: (Word, Word),
    parentNode :: Maybe Node -- Pode ser Nothing para a raiz da árvore
  } deriving (Show, Eq)

type Branch = Node

type BranchQueue = Seq.Seq Branch

type Basis = Map.Map (NonTerminal, NonTerminal) Bpa

data Bpa = Bpa1 Word | Bpa2 (Word, Word)

type GlobalState = State GlobalStateData

data GlobalStateData = TState
  { basis :: Basis
  ,  visitedPairs :: Set.Set (Word, Word)
  , normMap :: NormMap
  , grammar :: Grammar
  , log :: [String]
    -- ver log do haskell
  }

instance Show Bpa where
  show (Bpa1 n) = show n
  show (Bpa2 (n, m)) = show (n, m)

-- Functions created for the Monad type
-- Function to replace all elements in TStateData

replaceVisitedPairs :: Set.Set (Word, Word) -> GlobalState ()
replaceVisitedPairs newVisitedPairs =
  modify (\s -> s {visitedPairs = newVisitedPairs})

replaceBasis :: Basis -> GlobalState ()
replaceBasis b =
  modify (\s -> s {basis = b})

updateNormMap :: NormMap -> GlobalState ()
updateNormMap newMap = do
  modify (\s -> s {normMap = newMap})

-- Function to add a log message
addLog :: String -> State GlobalStateData ()
addLog msg = modify $ \s -> s {log = log s ++ [msg]}

-- Function to get the entire log
getFullLog :: State GlobalStateData [String]
getFullLog = gets log
