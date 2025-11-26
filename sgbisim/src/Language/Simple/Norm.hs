{- |
Module      :  Bisimulation.Norm
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module TODO
-}

module Language.Simple.Norm
  ( norm
  ) where

import Prelude hiding (Word, log)

import Language.Simple.State
import Language.Simple.Grammar

import Control.Monad (foldM)
import Control.Monad.State (gets, evalState)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

norm :: Word -> Bisimulation Norm
norm = norm' Set.empty
  where
    norm' :: Set.Set Nonterminal -> Word ->  Bisimulation Norm
    norm' _  []        = return (Normed 0)
    norm' vs w@(x : _) = do
      (nw, ys) <- computeNorm vs w x Set.empty
      modifyNormTable (\nt -> Set.foldr Map.delete nt ys)
      return nw
      where
        computeNorm _  []       _ ys = return (Normed 0, ys)
        computeNorm vs (x : xs) y ys =
          gets (Map.lookup x . normTable) >>= \case
            Just nx -> first (addNorm nx) <$> computeNorm vs xs y ys
            Nothing
              | x `elem` vs -> return (Unnormed, Set.insert y ys)
              | otherwise -> do
                let vs' = Set.insert x vs
                tbvs <- gets (Map.elems . transitions x . productions)
                if [] `elem` tbvs then do
                  modifyNormTable (Map.insert x (Normed 1))
                  first (addNorm (Normed 1)) <$> computeNorm vs' xs y ys
                else do
                  (nvs, ys') <- foldM (\(acc, ys'') w@(z:_) -> do
                      (nw, ys''') <- computeNorm vs' w z ys'' -- z used to be x
                      case nw of
                        Unnormed 
                          | head w /= x -> return (acc       , Set.insert x ys''')
                        _               -> return (min acc nw, ys'''             ))
                    (Unnormed, ys)
                    tbvs
                  let nx = nvs `addNorm` Normed 1
                  modifyNormTable (Map.insert x nx)
                  first (addNorm nx) <$> computeNorm vs' xs y ys'
