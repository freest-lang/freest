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

newtype Substitution = Θ [(Variable, Either T.KindedType K.Multiplicity)]
  deriving Show

instance Semigroup Substitution where
  Θ χtms1 <> Θ χtms2 = Θ (χtms1 ++ χtms2)
instance Monoid Substitution where
  mempty = Θ []

emptySubs :: Substitution
emptySubs = Θ []

subsMult :: Variable -> K.Multiplicity -> Substitution
subsMult χ m = Θ [(χ, Right m)]

subsType :: Variable -> T.KindedType -> Substitution
subsType χ t = Θ [(χ, Left t)]

applySubs :: Substitution -> T.KindedType -> T.KindedType
applySubs (Θ χtms) t = 
  foldr (\(χi, tmi) ti -> either (subst χi) (subsm χi) tmi ti) t χtms
  where
    subst χ t = \case
      T.Var _ _ χ' | isInstVar χ && χ == χ' -> t
      T.Abs s aks u -> T.Abs s aks (subst χ t u)
      T.App s u us -> T.App s (subst χ t u) (map (subst χ t) us)
      t -> t

    subsm χ m = \case
      T.Arrow s (K.VarM χ') | χ == χ' -> T.Arrow s m
      T.Abs s aks u -> T.Abs s aks $ subsm χ m u
      T.App s u us -> T.App s (subsm χ m u) (map (subsm χ m) us)

match :: E.KindedExp -> M.KindedModule -> T.KindedType -> T.KindedType
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
      -- M-IVar
      (T.Var s k χ, t2) | isInstVar χ -> do
        unless (T.kindOf t2 K.<: k) do
          throwE (KindMismatch (getSpan t2) k t2)
        return $ subsType χ t2
      (t1, T.Var s k χ) | isInstVar χ -> do
        unless (T.kindOf t1 K.<: k) do
          throwE (KindMismatch (getSpan t1) k t1)
        return $ subsType χ t1
      -- M-DualIVar
      (T.AppDual _ t1'@(T.Var _ _ χ), t2) | isInstVar χ ->
        match' e modl bindings visited t1' (T.AppDual (getSpan t2) t2)
      (t1, T.AppDual _ t2'@(T.Var _ _ χ)) | isInstVar χ ->
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
      (T.AppDual _ (T.AppVar _ a1 k1 t1s), T.AppDual _ (T.AppVar _ a2 k2 t2s))
        | (a1, a2) `Set.member` bindings && length t1s == length t2s
        -> foldMatch e modl bindings visited emptySubs t1s t2s
        | (isInstVar a1 || isInstVar a2) && length t1s == length t2s
        -> do
        θ <- match' e modl bindings visited (T.fromVariable a1 k1) (T.fromVariable a2 k2)
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
            (K.VarM χ, m2) | isInstVar χ -> return $ subsMult χ m2
            (m1, K.VarM χ) | isInstVar χ -> return $ subsMult χ m1
            (_, _) -> return emptySubs
          _ -> return emptySubs
        foldMatch e modl bindings visited θ t1s t2s
      -- M-Quant
      (T.AppQuant s1 p1 pk1 ((a1, k1) : aks1) t1', T.AppQuant s2 p2 pk2 ((a2, k2) : aks2) t2')
        | p1 == p2 && pk1 == pk2
        -> match' e modl (Set.insert (a1, a2) bindings) visited
            (T.AppQuant s1 p1 pk1 aks1 t1') (T.AppQuant s2 p2 pk2 aks2 t2')
      -- M-Var
      (T.AppVar _ a1 _ t1s, T.AppVar _ a2 _ t2s)
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
        Left  χ -> subsType χ (T.Void (getSpan χ) (K.uc (getSpan χ))) <> θ
        Right χ -> subsMult χ K.Un <> θ)
      emptySubs

  foldMatch e modl bindings visited θ t1s t2s = do
    x <- zipWithM (\t1i t2i -> (t1i, t2i,) <$> match' e modl bindings visited t1i t2i) t1s t2s 
    fold <$> zipWithM (match' e modl bindings visited) t1s t2s

fiv :: T.KindedType -> Set.Set (Either Variable Variable)
fiv = \case
  T.Var _ _ χ | isInstVar χ -> Set.singleton (Left χ)
  T.Arrow _ (K.VarM χ) | isInstVar χ -> Set.singleton (Right χ)
  T.Abs _ _ t -> fiv t
  T.App _ t ts -> Set.unions (fiv t : map fiv ts)
  _ -> Set.empty

isInstVar :: Variable -> Bool
isInstVar = (< -1) . internal

freshInstVar :: Span -> Validation Variable
freshInstVar s = do
  whileM ((< 1) <$> incCounter)
  i <- incCounter
  return $ Variable s ("χ" ++ show i) (- i)