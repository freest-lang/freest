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
  , runSynth, runSynth'
  , runCheck, runCheck'
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
synth :: M.ScopedModule -> KindCtx -> T.Type -> Validation Kind
synth mod ctx = \case
  -- Functional types
  T.Int s    -> pure (ut s)
  T.Float s  -> pure (ut s)
  T.Char s   -> pure (ut s)
  T.Arrow s m -> pure (Arrow s (lt s) (Arrow s (lt s) (Proper s m Top)))
  -- Session types
  T.Message s m _ -> pure (Arrow s (lt s) (if m == Lin then ls s else uc s))
  T.AppTypeMsg s _ a k t -> do
    (_, pk, _) <- checkSession mod (Map.insert a k ctx) t
    return (Proper s Lin pk)
  T.UnChoice s p ls -> pure (uc s)
  T.AppLinChoice s p lts -> do
    pk <- foldM (\pk (_,t) -> meet pk . (\(_, pk', _) -> pk') <$> checkSession mod ctx t) Session lts
    pure (Proper s Lin pk)
  T.End s _ -> pure (lc s)
  T.Skip s -> pure (us s)
  T.Void s k -> pure k
  T.AppSemi s t u -> do
    (m1, pk1, _) <- checkSession mod ctx t
    (m2, pk2, _) <- checkSession mod ctx u
    return $ Proper s (if pk1 == Channel then m1 else join m1 m2) (meet pk1 pk2) 
  T.AppDual s t -> do
    synthCheck mod ctx t (ls s)
  -- Polymorphism
  T.AppQuant s p aks t -> do
    (m, _, _) <- checkProper mod (Map.fromList aks `Map.union` ctx) t 
    return (Proper s m Top)
  -- Equations (including built-ins)
  T.TName s i -> lookupKind mod i
  T.Tuple s ts -> Proper s . fst <$> foldCheckProperJoin mod ctx Un ts <*> pure Top
  T.List s t -> (Proper s . (\(m, _, _) -> m) <$> checkProper mod ctx t) <*> pure Top
  T.DName s i -> lookupKind mod i
  -- Higher-order
  T.Var s a -> case ctx Map.!? a of
    Just k -> pure k
    Nothing -> do
      throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    k <- synth mod ctx t
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
        check mod ctx t' k' >> checkArgs s t k nargs npars ts' ks' kn
  T.Abs s aks t -> do
    flip (foldr (\(_, ki) k -> Arrow (spanFromTo ki k) ki k)) aks 
      <$> synth mod (Map.fromList aks `Map.union` ctx) t

-- | Check a type against a given kind.
check :: M.ScopedModule -> KindCtx -> T.Type -> Kind -> Validation ()
check mod ctx t k = void (synthCheck mod ctx t k)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: M.ScopedModule -> KindCtx -> Multiplicity -> [T.Type] 
                    -> Validation (Multiplicity, [T.Type])
foldCheckProperJoin mod ctx m = foldM checkProperJoin (m, [])
  where checkProperJoin (m', ts) t =
          checkProper mod ctx t  >>= \(m'',_ ,t) -> pure (join m' m'', ts ++ [t])

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProper :: M.ScopedModule -> KindCtx -> T.Type -> Validation (Multiplicity, Prekind, T.Type)
checkProper mod ctx t =
  synth mod ctx t >>= \case
    Proper _ m pk -> pure (m, pk, t)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: M.ScopedModule -> KindCtx -> T.Type -> Validation (Multiplicity, Prekind, T.Type)
checkSession mod ctx t = checkPrekind mod ctx t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: M.ScopedModule -> KindCtx -> T.Type -> Validation (Multiplicity, Prekind, T.Type)
checkChannel mod ctx t = checkPrekind mod ctx t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its 
-- minimal multiplicity and prekind. Otherwise, throw an error.
checkPrekind :: M.ScopedModule -> KindCtx -> T.Type -> Prekind 
             -> Validation (Multiplicity, Prekind, T.Type)
checkPrekind mod ctx t pk = do
  (m, pk', t') <- checkProper mod ctx t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk t' (Proper (getSpan t) m pk'))
  return (m, pk', t')

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

checkSubkindOfP' :: M.ScopedModule -> T.Type -> Kind -> Kind -> Validation ()
checkSubkindOfP' mod t k' k = do
  _ <- synth mod Map.empty t -- TODO: map empty
  unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t {- TODO: t' -} k)

-- | Synthesize the kind of a type and check if it is a subkind of another
-- kind.
synthCheck :: M.ScopedModule -> KindCtx -> T.Type -> Kind -> Validation Kind
synthCheck mod ctx t k = do
  k' <- synth mod ctx t
  checkSubkindOf t k' k
  return k'

-- | Check a module for type formation.
kindModule :: M.ScopedModule -> Validation M.KindedModule
kindModule mod = do
  tds <- Map.traverseWithKey kindTypeDecl (M.typeDecls mod)
  _ <- foldM kindDataConsDecls Map.empty $ Map.toList $ M.dataDecls mod -- TODO: foldrWithKeyM
  return mod{ M.kindSigs    = M.kindSigs mod
            , M.typeDecls   = tds
            , M.dataDecls   = M.dataDecls mod
            , M.consDecls   = M.consDecls mod
            , M.definitions = M.definitions mod
            }
  where 
    kindTypeDecl :: Identifier -> T.Type -> Validation T.Type
    kindTypeDecl i t = do
      k <- lookupKind mod i
      t' <- case t of
      -- TODO: I think synth is enough...
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
      check mod Map.empty t' k
      return t'

    kindDataConsDecls :: M.ConsDecls Kinded
                      -> (Identifier, ([(Variable, Kind)], [Identifier]))
                      -> Validation (M.ConsDecls Kinded)
    kindDataConsDecls cds' (i, (aks, cis)) = do
      k  <- lookupKind mod i
      cd <- checkDataDecl k id Map.empty aks k
      return (Map.union cd cds')
      where
        checkDataDecl :: Kind
                      -> (Kind -> Kind)
                      -> KindCtx
                      -> [(Variable, Kind)]
                      -> Kind
                      -> Validation (M.ConsDecls Kinded)
        checkDataDecl k f ctx [] _ = checkConsDecls k f ctx
        checkDataDecl k f ctx ((a, Var _ _) : aks') (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, k') : aks') (Arrow s k1 k2) = do
          checkSubkindOf (T.fromVariable a) k1 k'
          checkDataDecl k (f . Arrow s k') (Map.insert a k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls :: Kind
                       -> (Kind -> Kind)
                       -> KindCtx
                       -> Validation (M.ConsDecls Kinded)
        checkConsDecls k f ctx = do
          (m, cds') <- synthDataMult ctx cis
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (T.TName (getSpan i) i) k'))
          return cds'

        synthDataMult :: KindCtx
                      -> [Identifier]
                      -> Validation (Multiplicity, M.ConsDecls Kinded)
        synthDataMult ctx = foldM (\(m, acc) ci ->
          case M.consDecls mod Map.!? ci of
            Just (snd -> ts) -> do
              (m, ts') <- foldCheckProperJoin mod ctx m ts
              return (m, Map.insert ci (i, ts') acc)
            Nothing -> internalError ("constructor " ++ show ci ++ " not found"))
          (Un, Map.empty)

-- | Run kinding on a module, building the initial validation state from it.
-- This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the given module, otherwise.
runKindModule :: M.ScopedModule -> Either [Error] M.KindedModule
runKindModule m = runValidation emptyValidationState (kindModule m)

-- | Run synthesis on type, building the initial validation state from a given
-- module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * a kind synthesized from the type, otherwise.
runSynth :: M.KindedModule -> KindCtx -> T.Type -> Either [Error] Kind -- TODO: this function will be deprecated
runSynth mod ctx t = runValidation emptyValidationState (synth (M.asScoped mod) ctx t)

runSynth' :: M.KindedModule -> T.Type -> Either [Error] Kind -- TODO: this function will be deprecated
runSynth' mod t = runValidation emptyValidationState (synth (M.asScoped mod) Map.empty t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * unit, otherwise.
runCheck :: M.ScopedModule -> KindCtx -> T.Type -> Kind -> Either [Error] ()
runCheck mod ctx t k = runValidation emptyValidationState (check mod ctx t k)

runCheck' :: M.ScopedModule -> T.Type -> Kind -> Either [Error] ()
runCheck' mod t k = runValidation emptyValidationState (check mod Map.empty t k)