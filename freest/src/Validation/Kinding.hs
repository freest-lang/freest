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
  , runKindModule
  , runSynth
  )
where

import UI.Error
import Syntax.Base
import Syntax.Kind
import qualified Syntax.Module as M
import Syntax.Normalisation
import Syntax.Substitution (subs)
import qualified Syntax.Type as T
import Utils
import Validation.Base
import qualified Validation.Expose as Expose

import Data.Bifunctor (first)
import Data.Functor ((<&>))
import qualified Data.Map.Strict as Map
import Control.Monad.Extra (unlessM, (&&^))
import Data.Foldable.Extra (allM)
import Control.Monad.State (MonadState, foldM, unless, void, forM_, when, runState, StateT (runStateT), evalState, gets)
import Control.Monad.Trans.Except (throwE, runExceptT, ExceptT (ExceptT))
import Control.Monad.Identity (Identity(..))
import qualified Data.List.NonEmpty as NE

runKindModule :: M.Module -> Either [Error] M.Module
runKindModule m = runValidation (buildValidationState m) (kindModule m)

runSynth :: M.Module -> T.Type -> Either [Error] Kind
runSynth m t = runValidation (buildValidationState m) (synth Map.empty t)

kindModule :: M.Module -> Validation M.Module
kindModule m = do
  forM_ (M.typeDecls m) kindTypeDecl
  forM_ (M.dataDecls m) kindDataDecl
  -- kindDefs
  return m

kindTypeDecl :: (Identifier, ([Variable], T.Type)) -> Validation ()
kindTypeDecl (i, (as, t)) = do
  k <- lookupKind i
  checkTypeDecl k Map.empty as k
  where
    checkTypeDecl :: Kind -> KindingCtx -> [Variable] -> Kind -> Validation ()
    checkTypeDecl k ctx [] k' =
      check ctx t k'
    checkTypeDecl k ctx as Proper{} =
      throwE (ExpectsTooManyArgsK (getSpan i) i k)
    checkTypeDecl k ctx (a : as) (Arrow s k1 k2) =
      checkTypeDecl k (Map.insert a k1 ctx) as k2

kindDataDecl :: (Identifier, ([Variable], M.ConsDeclList)) -> Validation ()
kindDataDecl (i, (as, t)) = do
  k <- lookupKind i
  checkDataDecl k id Map.empty as k
  where
    checkDataDecl :: Kind -> (Kind -> Kind) -> KindingCtx -> [Variable] -> Kind -> Validation ()
    checkDataDecl k f ctx [] _ =
      checkConsDecls k f ctx t
    checkDataDecl k f ctx as Proper{} =
      throwE (ExpectsTooManyArgsK (getSpan i) i k)
    checkDataDecl k f ctx (a : as) (Arrow s k1 k2) =
      checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) as k2

    checkConsDecls :: Kind -> (Kind -> Kind) -> KindingCtx -> M.ConsDeclList -> Validation ()
    checkConsDecls k f ctx cds = do
      m <- synthDataMult ctx cds
      let k' = f (Proper (getSpan i) m Top)
      unless (k' <: k)
        (throwE (KindMismatch (getSpan i) k (T.TName (getSpan i) i) k'))

    synthDataMult ctx = foldM (synthConsMult ctx) Un

    synthConsMult ctx m (i, ts) = foldM (checkJoinConsField ctx) m ts

    checkJoinConsField ctx m' t =
      checkProper ctx t >>= \(m'',_) -> pure (join m' m'')

type KindingCtx = Map.Map Variable Kind

synth :: KindingCtx -> T.Type -> Validation Kind
synth ctx = \case
  -- Functional types
  T.Int s    -> pure (ut s)
  T.Float s  -> pure (ut s)
  T.Char s   -> pure (ut s)
  T.Arrow s m -> pure (Arrow s (lt s) (Arrow s (lt s) (Proper s m Top)))
  -- Session types
  T.Message s m _ -> pure (Arrow s (lt s) (Proper s m Session))
  T.Choice s m p lts -> do
    forM_ lts \(_,t) -> check ctx t (Proper s m Session)
    pure (Proper s m Session)
  T.End s _ -> pure (ls s)
  T.Skip s -> pure (us s)
  T.AppSemi s t u -> do
    -- k1 <- catchE (check' ctx t (ls s)) (putError (us s))
    -- k2 <- catchE (check' ctx u (ls s)) (putError (us s))
    k1 <- synthCheck ctx t (ls s)
    k2 <- synthCheck ctx u (ls s)
    return (join k1 k2)
  T.AppDual s t -> do
    -- catchE (check' ctx t (ls s)) (putError (us s))
    synthCheck ctx t (ls s)
  -- Polymorphism
  T.Quant s p a k t -> do
    checkProper (Map.insert a k ctx) t
    >>= \case (m,pk) -> pure (Proper s m pk)
  -- Equations
  T.TName s i -> lookupKind i
  T.DName s i -> lookupKind i
  -- Higher-order
  T.Var s a -> case ctx Map.!? a of
    Just k -> pure k
    Nothing -> putError (bot s) (OutOfScope s a)
  T.App s t ts -> do
    k <- synth ctx t
    let (ks,kn) = Expose.kArrow k
    checkArgs s t (length ts) (length ks) ts ks kn
  where
    checkArgs :: Span -> T.Type -> Int -> Int -- error info
              -> [T.Type] -> [Kind] -> Kind -> Validation Kind
    checkArgs _ _ _ _ [] ks' kn =
          pure (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks')
    checkArgs s t nargs npars _ [] _ =
      throwE (GivenTooManyArgsK s t nargs npars)
    checkArgs s t nargs npars (t' : ts') (k' : ks') kn =
      check ctx t' k' >> checkArgs s t nargs npars ts' ks' kn

-- synth :: KindingCtx -> T.Type -> Validation Kind
-- synth ctx t = do
--   k <- presynth ctx t
--   unlessM (valid t) $
--     throwE (InvalidType (getSpan t) t)
--   return k
--   where
--     -- valid   (T.Abs _ _ t)  = valid t -- TODO: Equations
--     valid w@(T.App _ t us) = normalises w &&^ valid t &&^ allM valid us
--     valid   _ = pure True

check :: KindingCtx -> T.Type -> Kind -> Validation ()
check ctx t k = void (synthCheck ctx t k)

checkProper :: KindingCtx -> T.Type -> Validation (Multiplicity, Prekind)
checkProper ctx t =
  synth ctx t >>= \case
    Proper _ m pk -> pure (m,pk)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

synthCheck :: KindingCtx -> T.Type -> Kind -> Validation Kind
synthCheck ctx t k = do
  k' <- synth ctx t
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')
  return k'

