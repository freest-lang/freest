module Validation.Matching where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import UI.Error 
import Validation.Base (Validation, incCounter)
import Validation.Normalisation (tNameRedex, isWhnf, reduce, normalise)

import Control.Monad (zipWithM, unless)
import Control.Monad.Extra (whileM)
import Control.Monad.Trans.Except
import Data.Foldable (fold)
import Data.List (sort)
import Data.Maybe (fromJust, isJust)
import Data.Set qualified as Set

-- | Instantiation-level substitution. Instantiation variables may occur as
-- types or as multiplicities.
newtype Substitution = Θ [(Variable, Either T.KindedType K.Multiplicity)]
  deriving Show

-- | Composition for substitutions.
instance Semigroup Substitution where
  Θ ivtms1 <> Θ ivtms2 = Θ (ivtms1 ++ ivtms2)

-- | The empty substitution.
instance Monoid Substitution where
  mempty = Θ []

-- | Alias for the empty substitution.
emptySubs :: Substitution
emptySubs = Θ []

-- | Make a multiplicity substitution.
subsMult :: Variable -> K.Multiplicity -> Substitution
subsMult iv m = Θ [(iv, Right m)]

-- | Make a type substitution.
subsType :: Variable -> T.KindedType -> Substitution
subsType iv t = Θ [(iv, Left t)]

-- | Apply a substitution.
applySubs :: Substitution -> T.KindedType -> T.KindedType
applySubs (Θ ivtms) t = 
  foldr (\(ivi, tmi) ti -> either (subst ivi) (subsm ivi) tmi ti) t ivtms
  where
    subst iv t = \case
      T.Var _ _ InstLv iv' | iv == iv' -> t
      T.Abs s aks u -> T.Abs s aks (subst iv t u)
      T.App s u us -> T.App s (subst iv t u) (map (subst iv t) us)
      t -> t

    subsm iv m = \case
      T.Arrow s (K.VarM InstLv iv') | iv == iv' -> T.Arrow s m
      T.Abs s aks u -> T.Abs s aks $ subsm iv m u
      T.App s u us -> T.App s (subsm iv m u) (map (subsm iv m) us)

-- | Find a substitution for instantiation variables that attempts
-- to make two given types equivalent. Adapted (heavily) from
-- https://doi.org/10.4204/EPTCS.420.1
match :: E.KindedExp -> M.KindedModule
      -> T.KindedType -> T.KindedType
      -> Validation Substitution
match e modl = match' e modl Set.empty Set.empty
  where
  match' e modl bindings visited t1 t2 =
    case (tNameRedex t1, tNameRedex t2) of
      (Just t1', _) | t1' `Set.member` visited -> return emptySubs
      (_, Just t2') | t2' `Set.member` visited -> return emptySubs
      _ -> match'' e modl bindings visited t1 t2

  match'' e modl bindings visited t1 t2 = do
    let fiv12 = fiv t1 `Set.union` fiv t2
    case (t1, t2) of
      -- M-FIV
      _ | Set.null fiv12 -> return emptySubs
      -- M-Inst
      (T.Var s k InstLv iv, t2) -> do
        unless (T.kindOf t2 K.<: k) do
          throwE (KindMismatch (getSpan t2) k t2)
        return $ subsType iv t2
      (t1, T.Var s k InstLv iv) -> do
        unless (T.kindOf t1 K.<: k) do
          throwE (KindMismatch (getSpan t1) k t1)
        return $ subsType iv t1
      -- M-DualInst
      (T.AppDual _ t1'@(T.Var _ _ InstLv iv), t2) ->
        match' e modl bindings visited t1' (T.AppDual (getSpan t2) t2)
      (t1, T.AppDual _ t2'@(T.Var _ _ InstLv iv)) ->
        match' e modl bindings visited (T.AppDual (getSpan t1) t1) t2'
      -- M-AbsorbSeqL/R
      (T.AppSemi _ (T.End _ p1) t1, T.End _ p2)
        | p1 == p2 -> return $ isubsAbsorbed fiv12
      (T.End _ p1, T.AppSemi _ (T.End _ p2) t2)
        | p1 == p2 -> return $ isubsAbsorbed fiv12
      (T.AppSemi _ (T.Void _ k1) t1, T.Void _ k2)
        | k1 == k2 -> return $ isubsAbsorbed fiv12
      (T.Void _ k1, T.AppSemi _ (T.Void _ k2) t2)
        | k1 == k2 -> return $ isubsAbsorbed fiv12
      (T.AppSemi _ (T.UnChoice _ p1 ls1) t1, T.UnChoice _ p2 ls2)
        | p1 == p2 && sort ls1 == sort ls2 -> return $ isubsAbsorbed fiv12
      (T.UnChoice _ p1 ls1, T.AppSemi _ (T.UnChoice _ p2 ls2) t2)
        | p1 == p2 && sort ls1 == sort ls2 -> return $ isubsAbsorbed fiv12
      -- M-MsgSeqL
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppMessage s m2 p2 t21)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' e modl bindings visited t11 t21
        θ2 <- case m1 of
          K.Lin -> match' e modl bindings visited t12 (T.Skip s)
          K.Un  -> return $ isubsAbsorbed (fiv t12)
        return $ θ2 <> θ1
      -- M-MsgSeqR
      (T.AppMessage s m1 p1 t11, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' e modl bindings visited t11 t21
        θ2 <- case m2 of
          K.Lin -> match' e modl bindings visited t22 (T.Skip s)
          K.Un  -> return $ isubsAbsorbed (fiv t22)
        return $ θ2 <> θ1
      -- M-Msg
      (T.AppMessage s m1 p1 t1', T.AppMessage _ m2 p2 t2')
        | m1 == m2 && p1 == p2
        -> match' e modl bindings visited t1' t2'
      -- M-MsgSeq
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' e modl bindings visited t11 t21
        θ2 <- case m1 of
          K.Lin -> match' e modl bindings visited t12 t22
          K.Un  -> return $ isubsAbsorbed (fiv t12)
        return $ θ2 <> θ1
      -- M-DualVar
      (T.AppDual _ (T.AppVar _ a1 k1 ObjLv t1s), T.AppDual _ (T.AppVar _ a2 k2 ObjLv t2s))
        | (a1, a2) `Set.member` bindings && length t1s == length t2s
        -> foldMatch e modl bindings visited emptySubs t1s t2s
      (T.AppDual _ (T.AppVar _ a1 k1 vm1 t1s), T.AppDual _ (T.AppVar _ a2 k2 vm2 t2s))
        | vm1 == vm2 && length t1s == length t2s
        -> do
        θ <- match' e modl bindings visited (T.Var (getSpan a1) k1 vm1 a1) (T.Var (getSpan a2) k2 vm2 a2)
        foldMatch e modl bindings visited θ t1s t2s
      -- M-Const (M-ArrowL/R)
      (T.App _ t1' t1s, T.App _ t2' t2s)
        |  T.isProper t1 && T.isProper t2
        && (  T.isAppArrow t1     && T.isAppArrow t2
           || T.isAppDName t1     && T.isAppDName t2
           || T.isAppLinChoice t1 && T.isAppLinChoice t2
            )
        -> do
        θ <- case (t1', t2') of
          (T.Arrow _ m1, T.Arrow _ m2) -> case (m1, m2) of
            (K.VarM InstLv iv, m2) -> return $ subsMult iv m2
            (m1, K.VarM InstLv iv) -> return $ subsMult iv m1
            (_, _) -> return emptySubs
          _ -> return emptySubs
        foldMatch e modl bindings visited θ t1s t2s
      -- M-Quant
      (T.AppQuant s1 p1 pk1 ((a1, k1) : aks1) t1', T.AppQuant s2 p2 pk2 ((a2, k2) : aks2) t2')
        | p1 == p2 && pk1 == pk2
        -> match' e modl (Set.insert (a1, a2) bindings) visited
            (T.AppQuant s1 p1 pk1 aks1 t1') (T.AppQuant s2 p2 pk2 aks2 t2')
      -- M-Var
      (T.AppVar _ a1 _ ObjLv t1s, T.AppVar _ a2 _ ObjLv t2s)
        | T.isProper t1 && T.isProper t2 && (a1, a2) `Set.member` bindings
        -> foldMatch e modl bindings visited emptySubs t1s t2s
      (t1, t2)
      -- M-RedexL
        | isJust (tNameRedex t1)
        -> match' e modl bindings (Set.insert (fromJust $ tNameRedex t1) visited) (normalise modl t1) t2
      -- M-RedexR
        | isJust (tNameRedex t2)
        -> match' e modl bindings (Set.insert (fromJust $ tNameRedex t2) visited) t1 (normalise modl t2)
      -- no matching for higher-kinded types
        | not (T.isProper t1)
        -> throwE (CannotInferHigherKindedTypeApp (getSpan e) (T.kindOf t1))
        | not (T.isProper t2)
        -> throwE (CannotInferHigherKindedTypeApp (getSpan e) (T.kindOf t2))
      -- M-ReduceL
        | not (isWhnf t1)
        -> match' e modl bindings visited (reduce modl t1) t2
      -- M-ReduceR
        | not (isWhnf t2)
        -> match' e modl bindings visited t1 (reduce modl t2)
      -- no match
        | otherwise -> return emptySubs

  isubsAbsorbed =
    foldl (\θ -> \case
        Left  iv -> subsType iv (T.Void (getSpan iv) (K.uc (getSpan iv))) <> θ
        Right iv -> subsMult iv K.Un <> θ)
      emptySubs

  foldMatch e modl bindings visited θ t1s t2s = do
    x <- zipWithM (\t1i t2i -> (t1i, t2i,) <$> match' e modl bindings visited t1i t2i) t1s t2s 
    fold <$> zipWithM (match' e modl bindings visited) t1s t2s

-- | The free instantiation variables in a type.
fiv :: T.KindedType -> Set.Set (Either Variable Variable)
fiv = \case
  T.Var _ _ InstLv iv -> Set.singleton (Left iv)
  T.Arrow _ (K.VarM InstLv iv) -> Set.singleton (Right iv)
  T.Abs _ _ t -> fiv t
  T.App _ t ts -> Set.unions (fiv t : map fiv ts)
  _ -> Set.empty

-- | Make a fresh type instantiation variable.
freshInstVarT :: Span -> K.Kind -> Validation T.KindedType
freshInstVarT s k = do
  i <- incCounter
  return $ T.Var s k InstLv (Variable s ("_a" ++ show i) i)

-- | Make a fresh multiplicity instantiation variable.
freshInstVarM :: Span -> Validation K.Multiplicity
freshInstVarM s = do
  i <- incCounter 
  return $ K.VarM InstLv (Variable s ("_m" ++ show i) i)
