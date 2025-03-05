{- |
Module      :  Validation.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}

module Validation.Kinding
  ( synth
  , check
  , checkSubkindOf
  , checkProper
  , checkSession
  , KindingCtx
  , kindModule
  , runKindModule
  , runSynth
  , runCheck
  )
where

import UI.Error
import Syntax.Base
import Syntax.Kind
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Utils
import Validation.Base
import Validation.Expose qualified as Expose
import Validation.Normalisation
import Validation.Substitution ( subs )

import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Extra ( unlessM, (&&^) )
import Control.Monad.State ( MonadState, foldM, unless, void, forM_, when, runState, StateT (runStateT), evalState, gets )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first )
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map

-- | The kinding context. Keeps track of type variables and their kinds.
type KindingCtx = Map.Map Variable Kind

-- | Synthesize the (minimal?) kind of a type.
synth :: KindingCtx -> T.Type -> Validation Kind
synth ctx = \case
  -- Functional types
  T.Int s    -> pure (ut s)
  T.Float s  -> pure (ut s)
  T.Char s   -> pure (ut s)
  T.Arrow s m -> pure (Arrow s (lt s) (Arrow s (lt s) (Proper s m Top)))
  -- Session types
  T.Message s m _ -> pure (Arrow s (lt s) (if m == Lin then ls s else uc s))
  T.SharedChoice s p ls -> pure (uc s)
  T.AppLinChoice s p lts -> do
    pk <- foldM (\pk (_,t) -> meet pk . snd <$> checkSession ctx t) Session lts
    pure (Proper s Lin pk)
  T.End s _ -> pure (lc s)
  T.Skip s -> pure (us s)
  T.Bottom s -> pure (uc s)
  T.AppSemi s t u -> do
    (m1, pk1) <- checkSession ctx t
    (m2, pk2) <- checkSession ctx u
    return $ Proper s (if pk1 == Channel then m1 else join m1 m2) (meet pk1 pk2) 
  T.AppDual s t -> do
    synthCheck ctx t (ls s)
  -- Polymorphism
  T.AppQuant s p aks t -> do
    checkProper (Map.fromList aks `Map.union` ctx) t
    >>= \case (m, Channel) -> pure (Proper s Lin Channel)
              (m, Session) -> pure (Proper s Lin Session)
              (m, Top    ) -> pure (Proper s m   Top    )
  -- Equations (including built-ins)
  T.TName s i -> lookupKind i
  T.Tuple s ts -> Proper s <$> foldCheckProperJoin ctx Un ts <*> pure Top
  T.List s t -> (Proper s . fst <$> checkProper ctx t) <*> pure Top
  T.DName s i -> lookupKind i
  -- Higher-order
  T.Var s a -> case ctx Map.!? a of
    Just k -> pure k
    Nothing -> do
      throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    k <- synth ctx t
    let (ks,kn) = Expose.kindArrow k
    checkArgs s t (length ts) (length ks) ts ks kn
  where
    checkArgs :: Span -> T.Type -> Int -> Int -- error info
              -> [T.Type] -> [Kind] -> Kind -> Validation Kind
    checkArgs _ _ _ _ [] ks' kn =
          pure (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks')
    checkArgs s t nargs npars _ [] _ =
      throwE (GivenTooManyArgsK s t npars nargs)
    checkArgs s t nargs npars (t' : ts') (k' : ks') kn =
      check ctx t' k' >> checkArgs s t nargs npars ts' ks' kn

-- | Check a type against a given kind.
check :: KindingCtx -> T.Type -> Kind -> Validation ()
check ctx t k = void (synthCheck ctx t k)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: KindingCtx -> Multiplicity -> [T.Type] -> Validation Multiplicity
foldCheckProperJoin ctx = foldM (checkProperJoin ctx)
  where checkProperJoin ctx m' t =
          checkProper ctx t >>= \(m'',_) -> pure (join m' m'')

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProper :: KindingCtx -> T.Type -> Validation (Multiplicity, Prekind)
checkProper ctx t =
  synth ctx t >>= \case
    Proper _ m pk -> pure (m,pk)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: KindingCtx -> T.Type -> Validation (Multiplicity, Prekind)
checkSession ctx t = do
  (m,pk) <- checkProper ctx t
  unless (pk <: Session) $
    throwE (SessionTypeMismatch (getSpan t) t (Proper (getSpan t) m pk))
  return (m,pk)

-- | Check if the kind of a type is a subkind of another. If not, throw an 
-- error located at the type.
checkSubkindOf :: T.Type -> Kind -> Kind -> Validation ()
checkSubkindOf t k' k = 
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')

-- | Synthesize the kind of a type and check if it is a subkind of another
-- kind.
synthCheck :: KindingCtx -> T.Type -> Kind -> Validation Kind
synthCheck ctx t k = do
  k' <- synth ctx t
  checkSubkindOf t k' k
  return k'

-- | Check a module for type formation.
kindModule :: M.Module -> Validation ()
kindModule m = do
  forM_ (M.typeDecls m) kindTypeDecl
  forM_ (M.dataDecls m) kindDataDecl
  where 
    kindTypeDecl :: (Identifier, T.Lambda T.Type) -> Validation ()
    kindTypeDecl (i, (map fst -> as, t)) = do
      k <- lookupKind i
      checkTypeDecl k Map.empty as k
      where
        checkTypeDecl k ctx [] k' =
          check ctx t k'
        checkTypeDecl k ctx as Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)
        checkTypeDecl k ctx (a : as) (Arrow s k1 k2) =
          checkTypeDecl k (Map.insert a k1 ctx) as k2

    kindDataDecl :: (Identifier, T.Lambda M.ConsDeclList) -> Validation ()
    kindDataDecl (i, (map fst -> as, t)) = do
      k <- lookupKind i
      checkDataDecl k id Map.empty as k
      where
        checkDataDecl k f ctx [] _ =
          checkConsDecls k f ctx t
        checkDataDecl k f ctx (a : as) (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) as k2
        checkDataDecl k f ctx as Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls k f ctx cds = do
          m <- synthDataMult ctx (map snd cds)
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (T.TName (getSpan i) i) k'))

        synthDataMult ctx = foldM (foldCheckProperJoin ctx) Un

-- | Run kinding on a module, building the initial validation state from it.
-- This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the given module, otherwise.
runKindModule :: M.Module -> Either [Error] M.Module
runKindModule m = 
  runValidation (buildValidationState m) (kindModule m) >> pure m

-- | Run synthesis on type, building the initial validation state from a given
-- module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * a kind synthesized from the type, otherwise.
runSynth :: M.Module -> T.Type -> Either [Error] Kind
runSynth m t = runValidation (buildValidationState m) (synth Map.empty t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * unit, otherwise.
runCheck :: M.Module -> T.Type -> Kind -> Either [Error] ()
runCheck m t k = runValidation (buildValidationState m) (check Map.empty t k)
