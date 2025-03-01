{- |
Module      :  Bisimulation.Norm
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module TODO
-}

module Language.Simple.Norm
  ( isNormed
  , norm
  , normUsingMap
  , nonterminals
  , reducesNorm
  )
where

import Language.Simple.Grammar
import Language.Simple.State

import Control.Monad.State
import Control.Applicative
import Data.Function ( on )
import Data.List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Prelude hiding ( Word, log )

nonterminals :: Grammar -> Set.Set NonTerminal
nonterminals (Grammar _ productions) = Set.union (Map.keysSet productions) (Set.fromList $ concatMap (concatMap snd . Map.toList) (Map.elems productions))

-- 1 Given a Grammar and a word indicates if the word is normed
isNormed :: Grammar -> Word -> Bool
isNormed g w = Data.Maybe.isJust (norm g w)

-- 2 Given a Grammar and a word returns the norm of the word
class Normalizable a where
  norm :: Grammar -> a -> IOF

instance Normalizable Word where
  norm g w = evalState (normUsingMap Set.empty w) initState
    where
      initState = TState {basis = Map.empty, visitedPairs = Set.empty, normMap = Map.empty, grammar = g, log = []}

instance Normalizable NonTerminal where
  norm g v = norm g [v]


normUsingMap :: Set.Set NonTerminal -> Word ->  GlobalState IOF
normUsingMap _ [] = return (Just 0)
normUsingMap visitedVars w@(v:vs) = do 
  (x,y) <- computeNorm visitedVars w v Set.empty
  deleteFromMap y
  return x


deleteFromMap :: Set.Set NonTerminal -> GlobalState ()
deleteFromMap vars = do
  map <- gets normMap
  let newMap = Set.foldr Map.delete map vars
  updateNormMap newMap


-- Calculates the norm using the NormMap
-- Receive a grammar, a word, a map and an array of "NonTerminals" (variables already visited)
-- Returns a tuple with the values of the norm, the variables already visited and the NormMap
computeNorm :: Set.Set NonTerminal -> Word-> NonTerminal -> Set.Set NonTerminal -> GlobalState (IOF, Set.Set NonTerminal)
computeNorm _ [] _ vars = return (Just 0, vars)
computeNorm visitedVars w@(v : vs) parent varsToRecheck = do
  -- troco a ordem e ponho o visitedVars como parametro
  map <- gets normMap
  case Map.lookup v map of
    Just nVar -> do
      (nTail, vars) <- computeNorm visitedVars vs parent varsToRecheck
      return (liftA2 (+) nTail nVar, vars)
    Nothing -> do
      if v `elem` visitedVars
        then do
          return (Nothing, Set.insert parent varsToRecheck)
        else do
          (Grammar _ prods) <- gets grammar
          wordNorm visitedVars prods w parent varsToRecheck

wordNorm :: Set.Set NonTerminal -> Productions -> Word -> NonTerminal -> Set.Set NonTerminal -> GlobalState (IOF, Set.Set NonTerminal)
wordNorm visitedVars prods (v : vs) parent varsToRecheck = do
  map <- gets normMap
  let newVisitedVars = Set.insert v visitedVars
      trans = transitions v prods
      toVisit = Map.elems trans -- ver se da para fazer sem listas/ noa consegui
  if [] `elem` toVisit
    then do
      let nVar = Just 1
      updateNormMap (Map.insert v nVar map)
      (nTail,vars) <- computeNorm newVisitedVars vs parent varsToRecheck
      return (liftA2 (+) nVar nTail,vars)
    else do
      (nVar,vars'') <-
        foldM
          ( \(acc,vars) w -> do
              (a,vars') <- computeNorm newVisitedVars w v vars
              case a of
                Nothing -> do 
                  if (head w) == v 
                    then
                      return (minWithInf acc a,vars')
                    else do 
                      addLog("nothing")
                      return (minWithInf acc a, Set.insert v vars')
                _ -> do
                  addLog("value")
                  return (minWithInf acc a,vars')
          )
          (Nothing,varsToRecheck)
          toVisit
      map <- gets normMap
      let nVar' = liftA2 (+) nVar (Just 1)
      updateNormMap (Map.insert v nVar' map)
      (nTail,vars''' )<- computeNorm newVisitedVars vs parent vars''
      return (liftA2 (+) nVar' nTail,vars''')

-- Auxiliary function of normUsingMap
-- normUsingMapAux ::  [Word] -> NormState IOF
-- normUsingMapAux [] = return Nothing
-- normUsingMapAux  (w:ws) = do
-- a <- normUsingMap w
--  b <- normUsingMapAux  ws
--  return (minWithInf a b)

-----------------------------------------------------------------------------------------------------------------------------

-- 3 Given a Grammar and a word returns the seminorm of the word
seminorm :: Grammar -> Word -> Int
seminorm g w = evalState (seminormUsingMap Set.empty w) initState
  where
    initState = TState {basis = Map.empty, visitedPairs = Set.empty, normMap = Map.empty, grammar = g, log = []}

-- Calculates the seminorm using the NormMap
-- Receive a grammar, a word, a map and an array of "NonTerminals" (variables already visited)
-- Returns a tuple with the values of the norm, the variables already visited and the NormMap
seminormUsingMap :: Set.Set NonTerminal -> Word -> GlobalState Int
seminormUsingMap _ [] = return 0
seminormUsingMap visitedVars (x : xs) = do
  result <- normUsingMap visitedVars [x]
  case result of
    Nothing -> return 0
    Just y -> do
      result' <- seminormUsingMap visitedVars xs
      return (y + result')

---------------------------------------------------------------------------------------------------------------------

-- 4 Calculates the k-th term in the canonical seminorm-reducing sequence of a word
-- requires 0 <= i <= seminorm g w
yk :: Grammar -> Word -> Int -> Word
yk g w i = evalState (ykUsingMap Set.empty i w) initState
  where
    initState = TState {basis = Map.empty, visitedPairs = Set.empty, normMap = Map.empty, grammar = g, log = []}

-- Calculates the  k-th term using the NormMap
-- Receive a grammar, a word, the k, a map and an array of "NonTerminals" (variables already visited)
-- Returns a word
ykUsingMap :: Set.Set NonTerminal -> Int -> Word -> GlobalState Word
ykUsingMap _ 0 w = return w
ykUsingMap visitedVars i (x : xs) = do
  result <- normUsingMap visitedVars [x]
  case result of
    Just n
      | n <= i -> ykUsingMap visitedVars (i - n) xs
      | n > i -> do
          map <- gets normMap
          (Grammar _ prods) <- gets grammar
          let trans = transitions x prods
              toVisit = Map.elems trans
              Just w = find (\word -> reducesNorm n (getNormWordFromMap word map)) toVisit
          ykUsingMap visitedVars (i - 1) (w ++ xs)

-----------------------------------------------------------------------------------------------------------------------------

-- 5 Calculate the valuation of a grammar
-- This function is not strictly necessary for the algorithm
valuation :: Grammar -> Int
valuation g@(Grammar _ p) = evalState (valuationUsingMap Set.empty words) initState
  where
    transList = Map.elems p
    words = concatMap Map.elems transList
    initState = TState {basis = Map.empty, visitedPairs = Set.empty, normMap = Map.empty, grammar = g, log = []}

-- Auxiliary function of valuation
valuationUsingMap :: Set.Set NonTerminal -> [Word] -> GlobalState Int
valuationUsingMap visitedVars = foldM (\acc w -> max acc <$> seminormUsingMap visitedVars w) 0

-----------------------------------------------------------------------------------------------------------------------------

-- Extra Functions
minWithInf :: IOF -> IOF -> IOF
minWithInf x Nothing = x
minWithInf Nothing x = x
minWithInf (Just x) (Just y) = Just (min x y)

reducesNorm :: Int -> Int -> Bool
reducesNorm x y = x == (y + 1)

getNormFromMap :: NonTerminal -> NormMap -> Int
getNormFromMap x mp = case Map.lookup x mp of
  Just val -> case val of
    Nothing -> -1
    Just x -> x
  Nothing -> undefined

getNormWordFromMap :: Word -> NormMap -> Int
getNormWordFromMap [] _ = 0
getNormWordFromMap [x] mp = getNormFromMap x mp
getNormWordFromMap (x : xs) mp = getNormFromMap x mp + getNormWordFromMap xs mp
