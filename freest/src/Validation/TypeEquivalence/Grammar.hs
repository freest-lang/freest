{- |
Module      :  TypeEquivalence.AlphaCongruence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Context-free grammars of a certain kind:

- Right-hand sides in productions are composed of (exactly) one terminal,
followed by a (possibly empty) word (a sequence of non-terminals)

- For each non-terminal symbol there is exactly one production.

This allows representing the productions of a grammar by a map from
non-terminals to a map from terminals to words.

-}

module Validation.TypeEquivalence.Grammar
  ( Terminal
  , NonTerminal
  , Word
  , Transitions
  , Productions
  , Grammar(..)
  , transitions
  , insertProduction
  , insertProductions
  , bottom
--, trans
  )
where

import           Syntax.Base
import qualified Data.Map.Strict         as M
import           Data.List               ( intercalate )
import           Prelude                 hiding ( Word )

-- Terminal symbols in the grammar
type Terminal = String

-- Non-terminal symbols in the grammar
type NonTerminal = Int

-- Words are strings of non-terminal symbols
type Word = [NonTerminal]

-- The transitions from a given non-terminal
type Transitions = M.Map Terminal Word

-- The productions of a grammar
type Productions = M.Map NonTerminal Transitions

-- The grammar, we have one initial word for each type that we convert together
data Grammar = Grammar [Word] Productions

-- Operations on grammars

class TransitionsFrom t where
  transitions :: t -> Productions -> Transitions

-- The transitions from a non-terminal
instance TransitionsFrom NonTerminal where
  transitions = M.findWithDefault M.empty

-- The transitions from a word
instance TransitionsFrom Word where
  transitions []       _ = M.empty
  transitions (x : xs) p = M.map (++ xs) (transitions x p)

-- Add a production X -> aw; the productions may already contain transitions for
-- the given nonterminal (hence the insertWith and union)
insertProduction :: NonTerminal -> Terminal -> Word -> Productions -> Productions
insertProduction x a w = M.insertWith M.union x (M.singleton a w)

insertProductions :: [(NonTerminal, Terminal, Word)]-> Productions -> Productions
insertProductions xs p =
  foldr (\(x, a, w) p -> insertProduction x a w p) p xs

-- The transitions from a word
-- trans :: Productions -> Word -> [Word]
-- trans p xs = M.elems (transitions xs p)

-- "⊥" - A nonterminal without transitions (up to clients to keep the invariant)
bottom :: NonTerminal
bottom = 0

-- Showing a grammar

instance Show Grammar where
  show (Grammar xss p) =
    "Start words: (" ++ intercalate ", " (map showWord xss) ++
    ")\nProductions (" ++ show nProds ++ " in total): " ++ showProductions p
    where nProds = M.foldr' (\t n -> M.size t + n) 0 p

-- Cannot be a flexible instance for there is an instance Show Map in module Map
showProductions :: Productions -> String
showProductions = M.foldrWithKey showTransitions ""
  where
    showTransitions :: NonTerminal -> Transitions -> String -> String
    showTransitions x m s = s ++ M.foldrWithKey (showTransition x) "" m

    showTransition :: NonTerminal -> Terminal -> Word -> String -> String
    showTransition x l xs s =
      s ++ "\n" ++ showNonTerminal x ++ " -> (" ++ l ++ ") " ++ showWord xs

showWord :: Word -> String
showWord w = intercalate " " (map showNonTerminal w)

-- Cannot be a flexible instance for there is an instance Show Int in the Prelude
showNonTerminal :: NonTerminal -> String
showNonTerminal 0 = "⊥"
showNonTerminal n = 'Y' : show n
