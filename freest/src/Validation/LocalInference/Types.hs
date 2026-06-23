-- Type matching for local type inference. Adapted (heavily) from 
-- Almeida et al., Local Type Inference for Context-Free Session Types
-- (https://doi.org/10.4204/EPTCS.420.1)

module Validation.LocalInference.Types where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Declarations qualified as D
import Syntax.Type.Kinded qualified as T
import UI.Error qualified as Error
import Validation.Base (Validation, incCounter)
import Validation.LocalInference.Multiplicities 
  (MultConstraints, kindEqConstraints, kindSubConstraints)
import Validation.LocalInference.Substitution
  (Substitution, emptySubs, subsMult, subsType)
import Validation.Normalisation 
  (tNameRedex, isWhnf, reduce, normalise)

import Control.Monad (zipWithM, unless)
import Control.Monad.Extra (whileM)
import Control.Monad.Trans.Except (throwE)
import Data.Foldable (fold)
import Data.List (sort)
import Data.Maybe (fromJust, isJust)
import Data.Set qualified as Set
import Data.Bifunctor (first)

-- | Find a substitution for instantiation variables that attempts to make two
-- types equivalent under a set of multiplicity constraints. Adapted (heavily)
-- from Almeida et al., Local Type Inference for Context-Free Session Types
-- (https://doi.org/10.4204/EPTCS.420.1)
match :: E.KindedExp -> D.KindedTypeDecls
      -> T.KindedType -> T.KindedType
      -> Validation (MultConstraints, Substitution)
match e tdecls = match' e tdecls Set.empty Set.empty
  where
  match' e tdecls bindings visited t1 t2 =
    case (tNameRedex t1, tNameRedex t2) of
      (Just t1', _) | t1' `Set.member` visited -> return ([], emptySubs)
      (_, Just t2') | t2' `Set.member` visited -> return ([], emptySubs)
      _ -> match'' e tdecls bindings visited t1 t2

  match'' e tdecls bindings visited t1 t2 = do
    let fiv12 = fiv t1 `Set.union` fiv t2
    case (t1, t2) of
      -- M-FIV
      _ | Set.null fiv12 -> return ([], emptySubs)
      -- M-Inst
      (T.Var s k InstLv iv, t2) ->
        return (kindSubConstraints (T.kindOf t2) k, subsType iv t2)
      (t1, T.Var s k InstLv iv) ->
        return (kindSubConstraints (T.kindOf t1) k, subsType iv t1)
      -- M-DualInst
      (T.AppDual _ t1'@(T.Var _ _ InstLv iv), t2) ->
        match' e tdecls bindings visited t1' (T.AppDual (getSpan t2) t2)
      (t1, T.AppDual _ t2'@(T.Var _ _ InstLv iv)) ->
        match' e tdecls bindings visited (T.AppDual (getSpan t1) t1) t2'
      -- M-AbsorbSeqL/R
      (T.AppSemi _ (T.End _ p1) t1, T.End _ p2)
        | p1 == p2 -> return ([], isubsAbsorbed fiv12)
      (T.End _ p1, T.AppSemi _ (T.End _ p2) t2)
        | p1 == p2 -> return ([], isubsAbsorbed fiv12)
      (T.AppSemi _ (T.Void _ k1) t1, T.Void _ k2)
        -> return (kindEqConstraints k1 k2, isubsAbsorbed fiv12)
      (T.Void _ k1, T.AppSemi _ (T.Void _ k2) t2)
        -> return (kindEqConstraints k1 k2, isubsAbsorbed fiv12)
      (T.AppSemi _ (T.UnChoice _ p1 ls1) t1, T.UnChoice _ p2 ls2)
        | p1 == p2 && sort ls1 == sort ls2 -> return ([], isubsAbsorbed fiv12)
      (T.UnChoice _ p1 ls1, T.AppSemi _ (T.UnChoice _ p2 ls2) t2)
        | p1 == p2 && sort ls1 == sort ls2 -> return ([], isubsAbsorbed fiv12)
      -- M-MsgSeqL
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppMessage s m2 p2 t21)
        | m1 == m2 && p1 == p2
        -> do
        mcsθ1 <- match' e tdecls bindings visited t11 t21
        mcsθ2 <- case m1 of
          K.Lin{} -> match' e tdecls bindings visited t12 (T.Skip s)
          K.Un{}  -> return ([], isubsAbsorbed (fiv t12))
        return $ mcsθ2 <> mcsθ1
      -- M-MsgSeqR
      (T.AppMessage s m1 p1 t11, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        mcsθ1 <- match' e tdecls bindings visited t11 t21
        mcsθ2 <- case m2 of
          K.Lin{} -> match' e tdecls bindings visited t22 (T.Skip s)
          K.Un{}  -> return ([], isubsAbsorbed (fiv t22))
        return $ mcsθ2 <> mcsθ1
      -- M-Msg
      (T.AppMessage s m1 p1 t1', T.AppMessage _ m2 p2 t2')
        | m1 == m2 && p1 == p2
        -> match' e tdecls bindings visited t1' t2'
      -- M-MsgSeq
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        mcsθ1 <- match' e tdecls bindings visited t11 t21
        mcsθ2 <- case m1 of
          K.Lin{} -> match' e tdecls bindings visited t12 t22
          K.Un{}  -> return ([], isubsAbsorbed (fiv t12))
        return $ mcsθ2 <> mcsθ1
      -- M-DualVar
      (T.AppDual _ (T.AppVar _ a1 k1 ObjLv t1s), T.AppDual _ (T.AppVar _ a2 k2 ObjLv t2s))
        | (a1, a2) `Set.member` bindings && length t1s == length t2s
        -> foldMatch e tdecls bindings visited ([], emptySubs) t1s t2s
      (T.AppDual _ (T.AppVar _ a1 k1 vm1 t1s), T.AppDual _ (T.AppVar _ a2 k2 vm2 t2s))
        | vm1 == vm2 && length t1s == length t2s
        -> do
        mcsθ <- match' e tdecls bindings visited (T.Var (getSpan a1) k1 vm1 a1)
                                               (T.Var (getSpan a2) k2 vm2 a2)
        foldMatch e tdecls bindings visited mcsθ t1s t2s
      -- M-Const (M-ArrowL/R)
      (T.App _ t1' t1s, T.App _ t2' t2s)
        |  T.isProper t1 && T.isProper t2
        && (  T.isAppArrow t1     && T.isAppArrow t2
           || T.isAppDName t1     && T.isAppDName t2
           || T.isAppLinChoice t1 && T.isAppLinChoice t2
            )
        -> foldMatch e tdecls bindings visited (mcs, emptySubs) t1s t2s
        where mcs = [(m1, m2) | (T.Arrow _ m1, T.Arrow _ m2) <- [(t1', t2')]]
      -- M-Quant
      (T.AppQuant s1 p1 pk1 m1 ((a1, k1) : aks1) t1', T.AppQuant s2 p2 pk2 m2 ((a2, k2) : aks2) t2')
        | p1 == p2 && pk1 == pk2
        -> first (mcs ++) <$> match' e tdecls (Set.insert (a1, a2) bindings) visited
            (T.AppQuant s1 p1 pk1 m1 aks1 t1') (T.AppQuant s2 p2 pk2 m2 aks2 t2')
        where mcs = kindEqConstraints k1 k2 ++ [(m1, m2) | p1 == T.In && pk1 == K.Top]
      -- M-Var
      (T.AppVar _ a1 _ ObjLv t1s, T.AppVar _ a2 _ ObjLv t2s)
        | T.isProper t1 && T.isProper t2 && (a1, a2) `Set.member` bindings
        -> foldMatch e tdecls bindings visited ([], emptySubs) t1s t2s
      (t1, t2)
      -- M-RedexL
        | isJust (tNameRedex t1)
        -> let visited' = Set.insert (fromJust $ tNameRedex t1) visited
            in match' e tdecls bindings visited' (normalise tdecls t1) t2
      -- M-RedexR
        | isJust (tNameRedex t2)
        -> let visited' = Set.insert (fromJust $ tNameRedex t2) visited 
            in match' e tdecls bindings visited' t1 (normalise tdecls t2)
      -- no matching for higher-kinded types
        | not (T.isProper t1)
        -> throwE (Error.CannotInferHigherKindedTypeApp (getSpan e) (T.kindOf t1))
        | not (T.isProper t2)
        -> throwE (Error.CannotInferHigherKindedTypeApp (getSpan e) (T.kindOf t2))
      -- M-ReduceL
        | not (isWhnf t1)
        -> match' e tdecls bindings visited (reduce tdecls t1) t2
      -- M-ReduceR
        | not (isWhnf t2)
        -> match' e tdecls bindings visited t1 (reduce tdecls t2)
      -- no match
        | otherwise -> return ([], emptySubs)

  isubsAbsorbed =
    foldl (\θ -> \case
        Left  iv -> subsType iv (T.Void (getSpan iv) (K.uc (getSpan iv))) <> θ
        Right iv -> subsMult iv (K.Un (getSpan iv)) <> θ)
      emptySubs

  foldMatch e tdecls bindings visited (mcs, θ) t1s t2s =
    (<> (mcs, θ)) . fold <$> zipWithM (match' e tdecls bindings visited) t1s t2s

-- | The free instantiation variables in a type.
fiv :: T.KindedType -> Set.Set (Either Variable Variable)
fiv = \case
  T.Var _ _ InstLv iv -> Set.singleton (Left iv)
  T.Arrow _ m -> fivm m
  T.AppForall _ m aks t -> Set.unions (fiv t : fivm m : map (fivk . snd) aks)
  T.AppExists _ aks t -> Set.unions (fiv t : map (fivk . snd) aks)
  T.ForallM _ m _ t -> fivm m `Set.union` fiv t
  T.Abs _ aks t -> Set.unions (fiv t : map (fivk . snd) aks)
  T.App _ t ts -> Set.unions (fiv t : map fiv ts)
  _ -> Set.empty
  where
  fivk = \case
    K.Proper _ m pk -> fivm m
    K.Arrow _ k1 k2 -> fivk k1 `Set.union` fivk k2
    _ -> Set.empty
  fivm = \case
    K.Sup _ lvφs -> Set.fromList (map (Right . snd) $ filter ((== InstLv) . fst) lvφs)
    _ -> Set.empty