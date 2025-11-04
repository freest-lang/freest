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
  , checkPrekind
  , checkSession
  , checkChannel
  , KindCtx
  , emptyKindCtx
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
import Control.Monad.State ( MonadState, foldM, unless, void, forM, forM_, when, runState, StateT (runStateT), evalState, gets, modify )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first )
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map

-- | The kinding context. Keeps track of type variables and their kinds.
type KindCtx = Map.Map Variable Kind

emptyKindCtx :: KindCtx
emptyKindCtx = Map.empty

-- | Synthesize the (minimal?) kind of a type.
synth :: KindCtx -> T.Type -> Validation Kind
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
  T.Void s k -> pure k
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
    checkArgs s t k (length ts) (length ks) ts ks kn
    where
      checkArgs :: Span -> T.Type -> Kind -> Int -> Int -- error info
                -> [T.Type] -> [Kind] -> Kind -> Validation Kind
      checkArgs _ _ _ _ _ [] ks' kn =
            pure (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks')
      checkArgs s t k nargs npars ts [] kn =
        throwE (GivenTooManyArgsK (spanFromTo (head ts) (last ts)) t kn npars nargs)
      checkArgs s t k nargs npars (t' : ts') (k' : ks') kn =
        check ctx t' k' >> checkArgs s t k nargs npars ts' ks' kn
  T.Abs s aks t -> do
    flip (foldr (\(_, ki) k -> Arrow (spanFromTo ki k) ki k)) aks 
      <$> synth (Map.fromList aks `Map.union` ctx) t

-- | Check a type against a given kind.
check :: KindCtx -> T.Type -> Kind -> Validation ()
check ctx t k = void (synthCheck ctx t k)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: KindCtx -> Multiplicity -> [T.Type] -> Validation Multiplicity
foldCheckProperJoin ctx = foldM (checkProperJoin ctx)
  where checkProperJoin ctx m' t =
          checkProper ctx t >>= \(m'',_) -> pure (join m' m'')

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProper :: KindCtx -> T.Type -> Validation (Multiplicity, Prekind)
checkProper ctx t =
  synth ctx t >>= \case
    Proper _ m pk -> pure (m,pk)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: KindCtx -> T.Type -> Validation (Multiplicity, Prekind)
checkSession ctx t = checkPrekind ctx t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: KindCtx -> T.Type -> Validation (Multiplicity, Prekind)
checkChannel ctx t = checkPrekind ctx t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its 
-- minimal multiplicity and prekind. Otherwise, throw an error.
checkPrekind :: KindCtx -> T.Type -> Prekind -> Validation (Multiplicity, Prekind)
checkPrekind ctx t pk = do
  (m, pk') <- checkProper ctx t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk t (Proper (getSpan t) m pk'))
  return (m, pk')

-- | Check if the kind of a type is a subkind of another. If not, throw an 
-- error located at the type.
checkSubkindOf :: T.Type -> Kind -> Kind -> Validation ()
checkSubkindOf t k' k = 
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')

-- | Check if the kind of a type is a subkind of another in a contravariant 
-- position. If not, throw an error located at the type.
checkSubkindOf' :: T.Type -> Kind -> Kind -> Validation ()
checkSubkindOf' t k' k =
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k' t k)

-- | Synthesize the kind of a type and check if it is a subkind of another
-- kind.
synthCheck :: KindCtx -> T.Type -> Kind -> Validation Kind
synthCheck ctx t k = do
  k' <- synth ctx t
  checkSubkindOf t k' k
  return k'

-- | Check a module for type formation.
kindModule :: M.Module -> Validation M.Module
kindModule m = do
  tds <- forM (M.typeDecls m) kindTypeDecl
  forM_ (M.dataDecls m) kindDataDecl
  modify (\s -> s{typeDecls = Map.fromList tds})
  return m{M.typeDecls = tds}
  where 
    kindTypeDecl :: (Identifier, T.Type) -> Validation (Identifier, T.Type)
    kindTypeDecl (i, t) = do
      k <- lookupKind i
      t' <- case t of
        T.Abs s aks u -> do
          aks' <- kindParams aks k
          return $ T.Abs s aks' u
          where
            kindParams ((a, Var _ _) : aks') (Arrow _ k1 k2) =
              ((a, k1) :) <$> kindParams aks' k2
            kindParams ((a, k) : aks') (Arrow _ k1 k2) = do
              checkSubkindOf' (T.Var (getSpan a) a) k1 k
              ((a, k) :) <$> kindParams aks' k2
            kindParams []  _ = pure []
            kindParams aks _ = 
              throwE (ExpectsTooManyArgsK (getSpan i) i k)
        t' -> return t'
      check Map.empty t' k
      return (i, t')

    kindDataDecl :: (Identifier, [(Variable, Kind)], M.ConsDeclList) -> Validation ()
    kindDataDecl (i, aks, t) = do
      k <- lookupKind i
      checkDataDecl k id Map.empty aks k
      where
        checkDataDecl k f ctx [] _ =
          checkConsDecls k f ctx t
        checkDataDecl k f ctx ((a, Var _ _) : aks') (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, k') : aks') (Arrow s k1 k2) = do
          checkSubkindOf' (T.Var (getSpan a) a) k1 k'
          checkDataDecl k (f . Arrow s k') (Map.insert a k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
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
  runValidation (buildValidationState m) (kindModule m)

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
