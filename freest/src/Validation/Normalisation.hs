{- |
Module      :  SimpleGrammar.Normalisation
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
  , betaRule
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Validation.Base ( unfold, getKind )
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
  -- W-Abs
  T.Abs{} -> True
  -- W-Seq1 _ semi-applied semicolon
  T.App _ T.Semi{} [_] -> True
  -- W-Seq2
  T.AppSemi _ t _ | isWhnf t && not (T.isAppSemi t || T.isSkip t || T.isAppLinChoice t || T.isAppTypeMsg t) -> True
  -- W-Dual
  T.AppDual _ T.Var{} -> True
  _ -> False

-- | One step type reduction. Requires 'not (isWnhf t)'.
reduce :: M.KindedModule -> T.KindedType -> T.KindedType
reduce mod = \case
  -- 1. Sequential composition
    -- R-Neut
  T.AppSemi _ T.Skip{} t -> t
    -- R-Assoc (must come before R.SemiL)
  T.AppSemi s1 (T.AppSemi s2 t1 t2) t3 -> T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
    -- R-ChoiceDist (must come before R.SemiL)
  T.AppSemi _ (T.AppLinChoice s p lts) u -> T.AppLinChoice s p (map (second \t -> T.AppSemi (getSpan t) t u) lts)
    -- R-QuantDist - Requires the kind of f. Implementing the particular case
    -- where the quantifier is followed by a lambda. This should be enforced by
    -- the parser and kept as an invariant. Reading the kind from the lambda.
  T.AppSemi s1 (T.App s2 (T.TypeMsg s3 p) [f]) u ->
    T.AppTypeMsg s1 p a k (T.AppSemi s2 (T.App s3 f [T.fromVariable a k]) u)
    where a = mkFreshVar s1 (freeVars f `Set.union` freeVars u)
          (K.Arrow _ k _) = T.kindOf f
    -- R-SemiL
  T.AppSemi s t u -> T.AppSemi s (reduce mod t) u

  -- 2. Dual
    -- R-DSkip
  T.AppDual _ t@T.Skip{} -> t
    -- R-DVoid
  T.AppDual _ t@T.Void{} -> t
    -- R-DEnd
  T.AppDual _ t@T.End{} -> T.dual t
    -- R-DMsg
  T.AppDual _ (T.App s u@T.Message{} ts) -> T.App s (T.dual u) ts
    -- R-DChoice, un
  T.AppDual s u@T.UnChoice{} -> T.dual u -- for *& and *+
    -- R-DChoice, lin
  T.AppDual s (T.AppLinChoice _ p lts) -> T.AppLinChoice s (T.dual p) (map (second $ T.AppDual s) lts)
    -- R-DQuant - Requires the kind of the quantifier. Implementing the
    -- particular case where the quantifier is followed by a lambda. This should
    -- be enforced by the parser and kept as an invariant. Reading the kind from
    -- the lambda.
  T.AppDual s1 t@(T.AppTypeMsg s2 p a k t') ->
    T.AppTypeMsg s1 (T.dual p) b k (T.AppDual s2 (subs a (T.fromVariable b k) t'))
    where b = mkFreshVar s1 (freeVars t)
    -- R-DSemi
  T.AppDual s1 (T.AppSemi s2 t1 t2) ->
    T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
    -- R-DDual
  T.AppDual _ (T.AppDual _ t) -> t
    -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce mod t)

  -- 3. β, μ, Void, AppL
    -- R-β
  T.App _ t@T.Abs{} us -> betaRule t us
    -- R-μ
  T.TName _ _ name -> unfold mod name
    -- R-VoidApp
  T.App s (T.Void _ (K.Arrow _ _ k)) _ -> T.Void s k
    -- R-TAppL
  T.App s t ts -> T.App s (reduce mod t) ts

  -- 4. Should not happen
  t -> internalError $ "Validation.Normalisation.reduce: Trying to reduce " ++ show t ++ ", a " ++ (if isWhnf t then "" else " non ") ++  "whnf"

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
      | reappears = T.Void (getSpan t) (K.image k)
      -- N-NotVisited + N-NoMuRedex
      | otherwise = norm visited' (reduce mod t)
      where
        u = tNameRedex t -- u is Maybe (µ∗U)
        reappears = maybe False   (`Set.member` visited) u
        visited'  = maybe visited (`Set.insert` visited) u
        k = case u of
          Just (T.AppTName _ name _) -> getKind mod name
          _ -> internalError $ "Validation.Normalisation.normalise: " ++ show u

-- | This is not exactly redexµ(T) = µκF. We must look at applied TNames, for
-- these are the types that reappear.
tNameRedex :: T.KindedType -> Maybe T.KindedType
tNameRedex = \case
  t@T.AppTName{}                               -> Just t -- µ∗U
  (T.AppSemi _ t@T.AppTName{} _)               -> Just t -- (µ∗U) ; V
  (T.AppDual _ t@T.AppTName{})                 -> Just t -- Dual (µ∗U)
  (T.AppSemi _ (T.AppDual _ t@T.AppTName{}) _) -> Just t -- (Dual (µ∗U)) ; V
  _                                            -> Nothing
