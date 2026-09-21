-- Type matching for local type inference. Adapted (heavily) from 
-- Almeida et al., Local Type Inference for Context-Free Session Types
-- (https://doi.org/10.4204/EPTCS.420.1)

module Validation.LocalInference.Types where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Declarations qualified as D
import Syntax.Type.Kinded qualified as T
import UI.Error qualified as Error
import Validation.Base (Validation, chaseShape, chaseShapeType, incCounter, addKindConstraint, addMultEquation, escapeTypeVar, escapedTypeVar, bindEscapedTypeVar)
import Syntax.Provenance (Origin(..), Reason(..))
import Validation.LocalInference.Multiplicities
  (MultConstraints, MultEquation(..), multEq, kindEqConstraints)
import Validation.LocalInference.Substitution
  (Substitution, emptySubs, subsType)
import Validation.Normalisation 
  (tNameRedex, isWhnf, reduce, normalise)

import Control.Monad (zipWithM, unless, when, forM_)
import Control.Monad.Extra (whileM)
import Control.Monad.Trans.Except (throwE)
import Data.Foldable (fold)
import Data.List (sort)
import Data.Maybe (fromJust, isJust)
import Data.Set qualified as Set

-- | Find a substitution for instantiation variables that attempts to make two
-- types equivalent, recording the multiplicity equations it needs. Adapted (heavily)
-- from Almeida et al., Local Type Inference for Context-Free Session Types
-- (https://doi.org/10.4204/EPTCS.420.1)
-- | The 'Span' is the application being matched: everything 'match' reports --
-- an escaped type argument bound to a polytype or out of scope, a higher-kinded
-- argument it cannot infer -- is located there, and nothing needs the
-- expression itself.
match :: Span -> D.KindedTypeDecls
      -> T.KindedType -> T.KindedType
      -> Validation Substitution
match sp tdecls t1__ t2__ = do
  t1z <- chaseShapeType t1__
  t2z <- chaseShapeType t2__
  match' sp tdecls Set.empty Set.empty t1z t2z
  where
  emit = mapM_ \(MultEquation l _ r _) -> addMultEquation (Origin AtApp sp) l r

  match' sp tdecls bindings visited t1 t2 =
    case (tNameRedex t1, tNameRedex t2) of
      (Just t1', _) | t1' `Set.member` visited -> return emptySubs
      (_, Just t2') | t2' `Set.member` visited -> return emptySubs
      _ -> match'' sp tdecls bindings visited t1 t2

  match'' sp tdecls bindings visited t1 t2 = do
    let fiv12 = fiv t1 `Set.union` fiv t2
    -- the operands' shapes as the state has them: a declaration unfolded out of
    -- 'tdecls' carries the kind the module gave it, which typing no longer
    -- settles in advance
    k1 <- chaseShape (T.kindOf t1)
    k2 <- chaseShape (T.kindOf t2)
    case (t1, t2) of
      -- M-FIV
      _ | Set.null fiv12 && not (openKinds t1 || openKinds t2) -> return emptySubs
      -- M-Inst
      (T.Var _ _ InstLv iv, t2) -> instVar iv t2
      (t1, T.Var _ _ InstLv iv) -> instVar iv t1
      -- M-DualInst
      (T.AppDual _ t1'@(T.Var _ _ InstLv iv), t2) ->
        match' sp tdecls bindings visited t1' (T.AppDual (getSpan t2) t2)
      (t1, T.AppDual _ t2'@(T.Var _ _ InstLv iv)) ->
        match' sp tdecls bindings visited (T.AppDual (getSpan t1) t1) t2'
      -- M-AbsorbSeqL/R
      (T.AppSemi _ (T.End _ p1) t1, T.End _ p2)
        | p1 == p2 -> return (isubsAbsorbed fiv12)
      (T.End _ p1, T.AppSemi _ (T.End _ p2) t2)
        | p1 == p2 -> return (isubsAbsorbed fiv12)
      (T.AppSemi _ (T.Void _ k1) t1, T.Void _ k2)
        -> isubsAbsorbed fiv12 <$ emit (kindEqConstraints k1 k2)
      (T.Void _ k1, T.AppSemi _ (T.Void _ k2) t2)
        -> isubsAbsorbed fiv12 <$ emit (kindEqConstraints k1 k2)
      (T.AppSemi _ (T.UnChoice _ p1 ls1) t1, T.UnChoice _ p2 ls2)
        | p1 == p2 && sort ls1 == sort ls2 -> return (isubsAbsorbed fiv12)
      (T.UnChoice _ p1 ls1, T.AppSemi _ (T.UnChoice _ p2 ls2) t2)
        | p1 == p2 && sort ls1 == sort ls2 -> return (isubsAbsorbed fiv12)
      -- M-MsgSeqL
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppMessage s m2 p2 t21)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' sp tdecls bindings visited t11 t21
        θ2 <- case m1 of
          K.Lin{} -> match' sp tdecls bindings visited t12 (T.Skip s)
          K.Un{}  -> return (isubsAbsorbed (fiv t12))
        return $ θ2 <> θ1
      -- M-MsgSeqR
      (T.AppMessage s m1 p1 t11, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' sp tdecls bindings visited t11 t21
        θ2 <- case m2 of
          K.Lin{} -> match' sp tdecls bindings visited t22 (T.Skip s)
          K.Un{}  -> return (isubsAbsorbed (fiv t22))
        return $ θ2 <> θ1
      -- M-Msg
      (T.AppMessage s m1 p1 t1', T.AppMessage _ m2 p2 t2')
        | m1 == m2 && p1 == p2
        -> match' sp tdecls bindings visited t1' t2'
      -- M-MsgSeq
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' sp tdecls bindings visited t11 t21
        θ2 <- case m1 of
          K.Lin{} -> match' sp tdecls bindings visited t12 t22
          K.Un{}  -> return (isubsAbsorbed (fiv t12))
        return $ θ2 <> θ1
      -- M-DualVar
      (T.AppDual _ (T.AppVar _ a1 k1 ObjLv t1s), T.AppDual _ (T.AppVar _ a2 k2 ObjLv t2s))
        | (a1, a2) `Set.member` bindings && length t1s == length t2s
        -> foldMatch sp tdecls bindings visited emptySubs t1s t2s
      (T.AppDual _ (T.AppVar _ a1 k1 vm1 t1s), T.AppDual _ (T.AppVar _ a2 k2 vm2 t2s))
        | vm1 == vm2 && length t1s == length t2s
        -> do
        θ <- match' sp tdecls bindings visited (T.Var (getSpan a1) k1 vm1 a1)
                                               (T.Var (getSpan a2) k2 vm2 a2)
        foldMatch sp tdecls bindings visited θ t1s t2s
      -- M-Const (M-ArrowL/R)
      (T.App _ t1' t1s, T.App _ t2' t2s)
        |  K.isProper k1 && K.isProper k2
        && (  T.isAppArrow t1     && T.isAppArrow t2
           || T.isAppDName t1     && T.isAppDName t2
           || T.isAppLinChoice t1 && T.isAppLinChoice t2
            )
        -> do
          emit [multEq m1 m2 | (T.Arrow _ m1, T.Arrow _ m2) <- [(t1', t2')]]
          foldMatch sp tdecls bindings visited emptySubs t1s t2s
      -- M-Quant
      (T.AppQuant s1 p1 bk1 m1 ((a1, k1) : aks1) t1', T.AppQuant s2 p2 bk2 m2 ((a2, k2) : aks2) t2')
        | p1 == p2 && bk1 == bk2
        -> do
            -- paired binder kinds must agree, and only kind inference still sees a
            -- binder variable: give it the multiplicity relation as two opposite
            -- bounds, over a common baseKind so no baseKind is constrained
            forM_ eqs \(MultEquation em1 eo em2 _) -> do
              addKindConstraint eo (K.Proper sp em1 K.Top) (K.Proper sp em2 K.Top)
              addKindConstraint eo (K.Proper sp em2 K.Top) (K.Proper sp em1 K.Top)
            emit mcs
            match' sp tdecls (Set.insert (a1, a2) bindings) visited
              (T.AppQuant s1 p1 bk1 m1 aks1 t1') (T.AppQuant s2 p2 bk2 m2 aks2 t2')
        where eqs = kindEqConstraints k1 k2
              mcs = eqs ++ [multEq m1 m2 | p1 == Neg && bk1 == K.Top]
      -- M-Var
      (T.AppVar _ a1 _ ObjLv t1s, T.AppVar _ a2 _ ObjLv t2s)
        | K.isProper k1 && K.isProper k2 && (a1, a2) `Set.member` bindings
        -> foldMatch sp tdecls bindings visited emptySubs t1s t2s
      (t1, t2)
      -- M-RedexL
        | isJust (tNameRedex t1)
        -> let visited' = Set.insert (fromJust $ tNameRedex t1) visited
            in match' sp tdecls bindings visited' (normalise tdecls t1) t2
      -- M-RedexR
        | isJust (tNameRedex t2)
        -> let visited' = Set.insert (fromJust $ tNameRedex t2) visited 
            in match' sp tdecls bindings visited' t1 (normalise tdecls t2)
      -- no matching for higher-kinded types
        | not (K.isProper k1)
        -> throwE (Error.CannotInferHigherKindedTypeApp sp k1)
        | not (K.isProper k2)
        -> throwE (Error.CannotInferHigherKindedTypeApp sp k2)
      -- M-ReduceL
        | not (isWhnf t1)
        -> match' sp tdecls bindings visited (reduce tdecls t1) t2
      -- M-ReduceR
        | not (isWhnf t2)
        -> match' sp tdecls bindings visited t1 (reduce tdecls t2)
      -- no match
        | otherwise -> return emptySubs

  -- an escaped variable is bound once, to an in-scope monotype; a fresh variable it meets is bound instead
  instVar iv t = escapedTypeVar iv >>= \case
    _ | T.Var _ _ InstLv iv' <- t, iv' == iv -> return emptySubs
    Nothing -> return (subsType iv t)
    Just entry | T.Var s k InstLv jv <- t -> escapedTypeVar jv >>= \case
      Nothing -> return (subsType jv (T.Var s k InstLv iv))
      Just _  -> bindEscaped iv entry t
    Just entry -> bindEscaped iv entry t

  bindEscaped iv (x, scope, stored) t = case stored of
    Just (u, _) -> (subsType iv u <>) <$> match sp tdecls u t
    Nothing -> do
      when (polytype t) $ throwE (Error.EscapedTypeArgPolymorphic sp x t)
      forM_ (Set.lookupMin (objVars t Set.\\ scope)) \a ->
        throwE (Error.EscapedTypeArgOutOfScope sp x a)
      -- the bound type's own instantiation variables belong to the application
      -- still running, and its local substitution never reaches the store:
      -- promote them as well, so that a later use binds them and the store's
      -- zonk, which is transitive, resolves this entry through them
      forM_ (fiv t) \iv' -> escapeTypeVar iv' x scope
      subsType iv t <$ bindEscapedTypeVar iv t sp

  polytype = \case
    T.AppForall{} -> True
    T.ForallM{}   -> True
    T.App _ u us  -> polytype u || any polytype us
    T.Abs _ _ u   -> polytype u
    _             -> False

  objVars = \case
    T.Var _ _ ObjLv a -> Set.singleton a
    T.Abs _ aks u     -> objVars u Set.\\ Set.fromList (map fst aks)
    T.App _ u us      -> Set.unions (objVars u : map objVars us)
    _                 -> Set.empty

  isubsAbsorbed = foldMap \iv -> subsType iv (T.Void (getSpan iv) (K.uc (getSpan iv)))

  foldMatch sp tdecls bindings visited θ t1s t2s =
    (<> θ) . fold <$> zipWithM (match' sp tdecls bindings visited) t1s t2s

-- | Whether a type still carries a solvable kind, baseKind or multiplicity.
-- Matching must not stop at a pair that does.
openKinds :: T.KindedType -> Bool
openKinds = \case
  T.Var _ k _ _         -> openK k
  T.Arrow _ m           -> openM m
  T.AppForall _ m aks t -> openM m || any (openK . snd) aks || openKinds t
  T.AppExists _ aks t   -> any (openK . snd) aks || openKinds t
  T.ForallM _ m _ t     -> openM m || openKinds t
  T.Abs _ aks t         -> any (openK . snd) aks || openKinds t
  T.App _ t ts          -> openKinds t || any openKinds ts
  _                     -> False
  where
    openK = \case
      K.Proper _ m bk -> openM m || openBK bk
      K.Arrow _ a b   -> openK a || openK b
      K.Var _ lv _    -> lv /= ObjLv
    openM = \case
      K.Sup _ as -> any ((/= ObjLv) . fst) as
      _          -> False
    openBK = \case
      K.VarBK lv _     -> lv /= ObjLv
      K.MeetBK bk1 bk2 -> openBK bk1 || openBK bk2
      K.JoinBK bk1 bk2 -> openBK bk1 || openBK bk2
      _                -> False

-- | The free type instantiation variables in a type.
fiv :: T.KindedType -> Set.Set Variable
fiv = \case
  T.Var _ _ InstLv iv -> Set.singleton iv
  T.AppForall _ _ _ t -> fiv t
  T.AppExists _ _ t -> fiv t
  T.ForallM _ _ _ t -> fiv t
  T.Abs _ _ t -> fiv t
  T.App _ t ts -> Set.unions (fiv t : map fiv ts)
  _ -> Set.empty