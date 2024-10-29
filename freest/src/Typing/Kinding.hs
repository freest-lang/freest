{- |
Module      :  Typing.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}

module Typing.Kinding
  ( synth
  , check
  , KindingCtx
  )
where

import IO.Error
import Syntax.Base
import Syntax.Kind
import Syntax.Normalisation
import qualified Syntax.Type as T
import Typing.Base

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Control.Monad.State (MonadState, foldM, unless, void, forM_, when)
import Control.Monad.Trans.Except
import Data.Bifunctor (first)
import qualified Data.Map as Map

type KindingCtx = Map.Map Variable Kind

presynth :: KindingCtx -> T.Type -> TypingExcept Kind
presynth ctx = \case
  -- Functional types
  T.Int s    -> pure (ut s)
  T.Float s  -> pure (ut s)
  T.Char s   -> pure (ut s)
  T.String s -> pure (ut s)
  T.Arrow s m -> pure (Arrow s (lt s) (lt s))
  T.Labelled s T.Variant lts -> do
    m  <- foldM joinMults Un (map snd lts)
    return (Proper s m Top)
  T.Tuple s ts -> do
    m  <- foldM joinMults Un ts
    return (Proper s m Top)
  -- Session types
  T.Message s m _ -> pure (Arrow s (lt s) (Proper s m Session))
  T.Labelled s (T.Choice m p) lts -> do
    forM_ lts \(_,t) -> check ctx t (Proper s m Session)
    pure (Proper s m Session)
  T.End s _ -> pure (ls s)
  T.Skip s -> pure (us s)
  T.Semi s t u -> do
    -- k1 <- catchE (check' ctx t (ls s)) (putError (us s))
    -- k2 <- catchE (check' ctx u (ls s)) (putError (us s))
    k1 <- check' ctx t (ls s)
    k2 <- check' ctx u (ls s)
    return (join k1 k2)
  T.Dual s t -> do
    -- catchE (check' ctx t (ls s)) (putError (us s))
    check' ctx t (ls s)
  -- Polymorphism
  T.Forall s aks t -> do
    check' (Map.union (Map.fromList aks) ctx) t (lt s)
    >>= \case Proper _ m _ -> pure (Proper s m Top)
  -- Equations
  T.Name s i -> fst <$> lookupType i
  -- Higher-order
  T.Var s a -> case ctx Map.!? a of
    Just k -> pure k
    Nothing -> putError (bot s) (OutOfScope s a)
  T.Abs s aks t ->
    foldr (fmap . Arrow s . snd)
      (presynth (Map.union (Map.fromList aks) ctx) t) aks
  T.App s t ts -> do
    k <- presynth ctx t
    let (pks,rk) = extractArrow k
    when (length ts > length pks) $
      throwE (TooManyArgsK s t k (length ts) (length pks))
    checkArgs ts pks rk
    where
      extractArrow (Arrow _ k1 k2) = 
        first (k1:) (extractArrow k2)
      extractArrow k = ([], k)
      checkArgs [] ks rk = 
        pure (foldr (\k k' -> Arrow (spanFromTo k k') k k') rk ks)
      checkArgs ts [] rk = 
        error "(Internal error) too many args exception not thrown."
      checkArgs (t:ts) (k:ks) rk =
        check ctx t k >> checkArgs ts ks rk
  -- Hole?
  T.Hole s -> pure (bot s)
  where
    joinMults m' t = do
      -- catchE (check' ctx t (lt s)) (putError (Proper s Un Top))
      check' ctx t (lt s) >>= \case Proper _ m pk -> pure (join m m')
      where s = getSpan t

synth :: KindingCtx -> T.Type -> TypingExcept Kind
synth ctx t = do
  k <- presynth ctx t
  unless (valid t) $
    throwE (InvalidType (getSpan t) t)
  return k
  where
    valid   (T.Abs _ _ t)  = valid t
    valid w@(T.App _ t us) = isNorm w && valid t && all valid us
    valid   _ = True

check' :: KindingCtx -> T.Type -> Kind -> TypingExcept Kind
check' ctx t k = do
  k' <- presynth ctx t
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')
  return k'

check :: KindingCtx -> T.Type -> Kind -> TypingExcept ()
check ctx t k = void (check ctx t k)
