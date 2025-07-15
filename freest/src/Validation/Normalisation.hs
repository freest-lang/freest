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
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap, ValidationState, getType, unfold, typeDecls, getKind )
import Validation.Substitution ( freeVars, subs, subsAll )
import Utils ( internalError )

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Debug.Trace ( trace )

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ t us
    | T.isConstant t && not (T.isSemi t || T.isTName t || T.isDual t || T.isVoid t) && length us >= 1 -> True
  -- W-Var
  T.AppVar{} -> True
  -- W-Abs
  T.Abs{} -> True
  -- W-Seq1 _ semi-applied semicolon
  T.App _ T.Semi{} [_] -> True
  -- W-Seq2
  T.AppSemi _ t _ | isWhnf t && not (T.isAppSemi t || T.isSkip t || T.isAppLinChoice t || T.isAppQuant t) -> True
  -- W-Dual
  T.AppDual _ T.Var{} -> True
  _ -> False

-- | One step type reduction. Requires 'not (isWnhf t)'.
reduce :: TypeDeclMap -> T.Type -> T.Type
reduce td = \case
  -- 1. Sequential composition
    -- R-Neut
  T.AppSemi _ T.Skip{} t -> t
    -- R-Assoc (must come before R.SemiL)
  T.AppSemi s1 (T.AppSemi s2 t1 t2) t3 -> T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
    -- R-ChoiceDist (must come before R.SemiL)
  T.AppSemi _ (T.App s t@T.Choice{} us) v -> T.App s t (map (\u -> T.AppSemi (getSpan u) u v) us)
    -- R-QuantDist - Requires the kind of the quantifier. Implementing the
    -- particular case where the quantifier is followed by a lambda. This should
    -- be enforced by the parser and kept as an invariant. Reading the kind from
    -- the lambda.
  T.AppSemi s1 (T.App s2 (T.Quant s3 p) [f]) u ->
    T.AppQuant s1 p [(a,k)] (T.AppSemi s2 (T.App s3 f [T.fromVariable a]) u)
    where a = freshVariable s1 (freeVars f `Set.union` freeVars u)
          k = kindOfLambda f
    -- R-SemiL
  T.AppSemi s t u -> T.AppSemi s (reduce td t) u
  
  -- 2. Dual
    -- R-DSkip
  T.AppDual _ t@T.Skip{} -> t
    -- R-DEnd
  T.AppDual _ t@T.End{} -> T.dual t
    -- R-DVoid
  T.AppDual _ t@T.Void{} -> t
    -- R-DMsg
  T.AppDual _ (T.App s u@T.Message{} ts) -> T.App s (T.dual u) ts
    -- R-DChoice (un and lin)
  T.AppDual s u@T.Choice{} -> T.dual u -- for *& and *+
  T.AppDual s (T.App _ u@T.Choice{} ts) ->  T.App s (T.dual u) (map (T.AppDual s) ts)
    -- R-DQuant - Requires the kind of the quantifier. Implementing the
    -- particular case where the quantifier is followed by a lambda. This should
    -- be enforced by the parser and kept as an invariant. Reading the kind from
    -- the lambda.
  T.AppDual s1 (T.App s2 (T.Quant s3 p) [f]) ->
    T.AppQuant s1 (T.dual p) [(a,k)] (T.AppDual s2 (T.App s3 f [T.fromVariable a]))
    where a = freshVariable s1 (freeVars f)
          k = kindOfLambda f
    -- R-DSemi
  T.AppDual s1 (T.AppSemi s2 t1 t2) -> T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
    -- -- R-DDual
  T.AppDual _ (T.AppDual _ t) -> t
    -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce td t)
  
  -- 3. β, Void, AppL, and μ
    -- R-β
  T.App _ t@T.Abs{} us -> betaRule t us
    -- R-VoidApp
  T.App s (T.Void _ (K.Arrow _ _ k)) _ -> T.Void s k
    -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
    -- R-μ
  t@(T.TName _ name) -> unfold td name
  t -> internalError $ "Validation.Normalisation.reduce: Trying to reduce " ++ show t ++ ", a " ++ (if isWhnf t then "" else " non ") ++  "whnf"

-- | requires: t is an abstraction with a single binder
kindOfLambda :: T.Type -> K.Kind
kindOfLambda (T.Abs _ [(_,k)] _) = k
kindOfLambda t = internalError $ "Validation.Normalisation.kindOfLambda: " ++ show t

freshVariable :: Span -> Set.Set Variable -> Variable -- TODO:review
freshVariable s fvs = freshVar (mkDefaultVar "β" s) fvs

-- | Type application, the beta rule.
-- (λα1...αn. T) U1 ... Um -->β
--     T[U1/α1]...[Un/αn]                  if n = m
--     (T[U1/α1]...[Un/αn]) Un+1 ... Um    if m > n
--     λαn+1...αm. T[U1/α1]...[Un/αn]      if n > m
betaRule :: T.Type -> [T.Type] -> T.Type
betaRule (T.Abs s aks t) us
  | n == m    = v
  | m > n     = T.App s v (drop n us)
  | otherwise = T.Abs s (drop m aks) v
  where n = length aks
        m = length us
        v = subsAll (map fst aks) us t

-- | The weak head normal form of a type. Big-step semantics. A total function for
-- well-formed types.
normalise :: ValidationState -> T.Type -> T.Type
normalise vs = norm Set.empty
  where
    norm :: Set.Set T.Type -> T.Type -> T.Type
    norm visited t
      -- N-Whnf
      | isWhnf t = t
      -- N-Visited
      | reappears = T.Void (getSpan t) (K.image k)
      -- N-NotVisited + N-NoMuRedex
      | otherwise = trace ("reducing " ++ show t) $ norm visited' (reduce (typeDecls vs) t)
      where
        u = tNameRedex t -- u is Maybe (µ∗U)
        reappears = maybe False   (`Set.member` visited) u
        visited'  = maybe visited (`Set.insert` visited) u
        k = case u of
          Just (T.AppTName _ name _) -> getKind vs name
          _ -> internalError $ "Validation.Normalisation.normalise: " ++ show u

-- | This is not exactly redexµ(T) = µκF. We must look at applied TNames, for
-- these are the types that reappear.
tNameRedex :: T.Type -> Maybe T.Type
tNameRedex = \case
  t@T.AppTName{}                               -> Just t -- µ∗U
  (T.AppSemi _ t@T.AppTName{} _)               -> Just t -- (µ∗U) ; V
  (T.AppDual _ t@T.AppTName{})                 -> Just t -- Dual (µ∗U)
  (T.AppSemi _ (T.AppDual _ t@T.AppTName{}) _) -> Just t -- (Dual (µ∗U)) ; V
  _                                            -> Nothing
