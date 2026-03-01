{- |
Module      :  Validation.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types

Weak reduction strategies do not reduce under lambda abstractions.

-}

module Validation.Normalisation
  ( isWhnf
  , reduce
  , normalise
  , tNameRedex
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Validation.Base ( unfold )
import Validation.Substitution ( freeVars, subs, subsAll )
import Utils ( internalError )

import Data.Bifunctor (second)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Debug.Trace ( trace )

-- | Is a given type a weak head normal form?
isWhnf :: T.KindedType -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ t us
    | T.isConstant t && not (T.isSemi t || T.isTName t || T.isDual t || T.isVoid t) && not (null us) -> True
  -- W-Var
  T.AppVar{} -> True
  -- W-Dual
  T.AppDual _ T.AppVar{} -> True
  -- W-Abs
  T.Abs{} -> True
  -- W-Seq1 _ semi-applied semicolon
  T.App _ T.Semi{} [_] -> True
  -- W-Seq2
  T.AppSemi _ T.End{}                  _ -> True
  T.AppSemi _ T.Void{}                 _ -> True
  T.AppSemi _ T.AppMessage{}           _ -> True
  T.AppSemi _ T.AppVar{}               _ -> True
  T.AppSemi _ (T.AppDual _ T.AppVar{}) _ -> True
  T.AppSemi _ T.UnChoice{}             _ -> True -- Extra
  -- Otherwise
  _ -> False

-- | One step type reduction (aka, the tau rules).
--   Requires 'not (isWnhf t)'.
reduce :: M.KindedModule -> T.KindedType -> T.KindedType
reduce mod = \case
  -- 1. Sequential composition, the R-S* rules
    -- R-SNeut
  T.AppSemi _ T.Skip{} t -> t
    -- R-SAssoc (see W-Seq2)
  T.AppSemi s1 (T.AppSemi s2 t@T.End{} u) v                  -> T.AppSemi s1 t (T.AppSemi s2 u v)
  T.AppSemi s1 (T.AppSemi s2 t@T.Void{} u) v                 -> T.AppSemi s1 t (T.AppSemi s2 u v)
  T.AppSemi s1 (T.AppSemi s2 t@T.AppMessage{} u) v           -> T.AppSemi s1 t (T.AppSemi s2 u v)
  T.AppSemi s1 (T.AppSemi s2 t@T.AppVar{} u) v               -> T.AppSemi s1 t (T.AppSemi s2 u v)
  T.AppSemi s1 (T.AppSemi s2 t@(T.AppDual _ T.AppVar{}) u) v -> T.AppSemi s1 t (T.AppSemi s2 u v)
    -- R-SChoiceDist
  T.AppSemi _ (T.AppLinChoice s p lts) u ->
    T.AppLinChoice s p (map (second \t -> T.AppSemi (getSpan t) t u) lts)
    -- R-SQuantDist (We may have a simpler version if Quant is always followed by Abs)
  T.AppSemi s1 (T.App s2 q@T.QuantS{} [f]) u ->
    T.App s1 q [T.Abs s1 [(a,k)] (T.AppSemi s2 (T.App s2 f [T.fromVariable a k]) u)]
    where a = mkFreshVar s1 (freeVars f `Set.union` freeVars u)
          (K.Arrow _ k _) = T.kindOf q
    -- R-SemiL
  T.AppSemi s t u -> T.AppSemi s (reduce mod t) u

  -- 2. Dual, the R-D* rule
    -- R-DSkip
  T.AppDual _ t@T.Skip{} -> t
    -- R-DVoid
  T.AppDual _ t@T.Void{} -> t
    -- R-DEnd
  T.AppDual _ t@T.End{} -> T.dual t
    -- R-DMsg
  T.AppDual _ (T.App s u@T.Message{} ts) -> T.App s (T.dual u) ts
    -- R-DChoice, un
  T.AppDual _ u@T.UnChoice{} -> T.dual u -- for *& and *+
    -- R-DChoice, lin
  T.AppDual s (T.AppLinChoice _ p lts) -> T.AppLinChoice s (T.dual p) (map (second $ T.AppDual s) lts)
    -- R-DQuant
  T.AppDual s1 (T.App s2 (T.QuantS s3 (K.Arrow _ (K.Arrow _ k _) _) p) [f]) ->
    T.AppQuantS s1 (T.dual p) a k (T.AppDual s2 (T.App s3 f [T.fromVariable a k]))
    where a = mkFreshVar s1 (freeVars f)
    -- R-DSemi
  T.AppDual s1 (T.AppSemi s2 t1 t2) ->
    T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
    -- R-DDual
  T.AppDual _ (T.AppDual _ t) -> t
    -- R-DAppR
  T.AppDual s t -> T.AppDual s (reduce mod t)

  -- 3. β, μ, Void, AppL
    -- R-β
  T.App _ t@T.Abs{} us -> betaRule t us
    -- R-μ
  T.TName _ _ name -> unfold mod name
    -- R-Void
  T.App s (T.Void _ (K.Arrow _ _ k)) _ -> T.Void s k
    -- R-AppL
  T.App s f ts -> T.App s (reduce mod f) ts

  -- 4. Should not happen
  t -> internalError $ "Validation.Normalisation.reduce: Trying to reduce " ++ show t ++ ", a " ++ (if isWhnf t then "" else " non ") ++  "whnf"

-- | The weak head normal form of a type. Big-step semantics. A total function for
-- well-formed types.
normalise :: M.KindedModule -> T.KindedType -> T.KindedType
normalise mod = norm Set.empty
  where
    norm :: Set.Set T.KindedType -> T.KindedType -> T.KindedType
    norm visited t
      -- N-Whnf
      | isWhnf t = t
      -- N-Visited
      | reappears = T.Void (getSpan t) (T.kindOf t)
      -- N-NotVisited + N-NoMuRedex
      | otherwise = norm visited' (reduce mod t)
      where
        u = tNameRedex t -- u is Maybe (µ∗F)
        reappears = maybe False   (`Set.member` visited) u
        visited'  = maybe visited (`Set.insert` visited) u
        span = getSpan t

-- | The 𝜇-redex extraction. Partial function; hence the Maybe
tNameRedex :: T.KindedType -> Maybe T.KindedType
tNameRedex = \case
  t@T.AppTName{}               -> Just t -- µ∗F
  (T.AppDual _ t@T.AppTName{}) -> Just t -- Dual (µ∗F)
  (T.AppSemi _ t _)            -> tNameRedex t -- T; U
  _                            -> Nothing

-- | Type application, the beta rule.
-- (λα1...αn. T) U1 ... Um -->β
--     T[U1/α1]...[Un/αn]                  if n = m
--     (T[U1/α1]...[Un/αn]) Un+1 ... Um    if m > n
--     λαn+1...αm. T[U1/α1]...[Un/αn]      if n > m
betaRule :: T.KindedType -> [T.KindedType] -> T.KindedType
betaRule (T.Abs s aks t) us
  | n == m    = v
  | m > n     = T.App s v (drop n us)
  | otherwise = T.Abs s (drop m aks) v
  where n = length aks
        m = length us
        v = subsAll (map fst aks) us t
