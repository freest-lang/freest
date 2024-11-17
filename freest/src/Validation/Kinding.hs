{- |
Module      :  Validation.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}

module Validation.Kinding
  ( synth
  , check
  , KindingCtx
  , runKinding
  )
where

import UI.Error
import Syntax.Base
import Syntax.Kind
import qualified Syntax.Module as M
import Syntax.Normalisation
import qualified Syntax.Type as T
import Utils
import Validation.Base

import Data.Bifunctor (first)
import Data.Functor ((<&>))
import qualified Data.Map.Strict as Map
import Control.Monad.Extra (unlessM, (&&^))
import Data.Foldable.Extra (allM)
import Control.Monad.State (MonadState, foldM, unless, void, forM_, when, runState, StateT (runStateT), evalState)
import Control.Monad.Trans.Except (throwE, runExceptT, ExceptT (ExceptT))
import Control.Monad.Identity (Identity(..))
import qualified Data.List.NonEmpty as NE

runKinding :: M.Module -> Either [Error] M.Module
runKinding m =
  let s = ValidationState {errors = [], kindCtx = Map.empty, typeEqs = Map.empty} in 
  let (x,ValidationState{errors}) = runState (runExceptT kindModule) s
  in case x of 
    Left e                -> Left (errors++[e])
    Right _ | null errors -> Right m
            | otherwise   -> Left errors 

kindModule :: Validation ()
kindModule = undefined

type KindingCtx = Map.Map Variable Kind

presynth :: KindingCtx -> T.Type -> Validation Kind
presynth ctx = \case
  -- Functional types
  T.Int s    -> pure (ut s)
  T.Float s  -> pure (ut s)
  T.Char s   -> pure (ut s)
  T.Arrow s m -> pure (Arrow s (lt s) (lt s))
  T.Labelled s l lts | l == T.Record || l == T.Variant -> do
    m  <- foldM joinMults Un (map snd lts)
    return (Proper s m Top)
  -- Session types
  T.Message s m _ -> pure (Arrow s (lt s) (Proper s m Session))
  T.Labelled s (T.Choice m p) lts -> do
    forM_ lts \(_,t) -> check ctx t (Proper s m Session)
    pure (Proper s m Session)
  T.End s _ -> pure (ls s)
  T.Skip s -> pure (us s)
  T.AppSemi s t u -> do
    -- k1 <- catchE (check' ctx t (ls s)) (putError (us s))
    -- k2 <- catchE (check' ctx u (ls s)) (putError (us s))
    k1 <- presynthCheck ctx t (ls s)
    k2 <- presynthCheck ctx u (ls s)
    return (join k1 k2)
  T.AppDual s t -> do
    -- catchE (check' ctx t (ls s)) (putError (us s))
    presynthCheck ctx t (ls s)
  -- Polymorphism
  T.Forall s a k t -> do
    presynthCheck (Map.insert a k ctx) t (lt s)
    >>= \case Proper _ m _ -> pure (Proper s m Top)
  -- Equations
  T.Name s i -> lookupKind i
  -- Higher-order
  T.Var s a -> case ctx Map.!? a of
    Just k -> pure k
    Nothing -> putError (bot s) (OutOfScope s a)
  T.App s t ts -> do
    k <- presynth ctx t
    let (ks,kn) = extractArrow k
        checkArgs [] ks' =
          pure (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks')
        checkArgs _ [] =
          throwE (TooManyArgsK s t k (length ts) (length ks))
        checkArgs (t' : ts') (k':ks') =
          check ctx t' k' >> checkArgs ts' ks'
    checkArgs (NE.toList ts) ks
    where
      extractArrow (Arrow _ k1 k2) =
        first (k1:) (extractArrow k2)
      extractArrow k = ([], k)
  where
    joinMults m' t = do
      -- catchE (check' ctx t (lt s)) (putError (Proper s Un Top))
      presynthCheck ctx t (lt s) >>= \case Proper _ m pk -> pure (join m m')
      where s = getSpan t

synth :: KindingCtx -> T.Type -> Validation Kind
synth ctx t = do
  k <- presynth ctx t
  unlessM (valid t) $
    throwE (InvalidType (getSpan t) t)
  return k
  where
    -- valid   (T.Abs _ _ t)  = valid t -- TODO: Equations
    valid w@(T.App _ t us) = normalises w &&^ valid t &&^ allM valid us
    valid   _ = pure True

check :: KindingCtx -> T.Type -> Kind -> Validation ()
check ctx t k = void (presynthCheck ctx t k)

presynthCheck :: KindingCtx -> T.Type -> Kind -> Validation Kind
presynthCheck ctx t k = do
  k' <- presynth ctx t
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')
  return k'

