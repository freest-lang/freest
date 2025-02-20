{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types

Weak reduction strategies do not reduce under lambda abstractions.

-}

module Validation.Normalisation
  ( normalise
  , isWhnf -- for testing
  , reduce -- for testing
  )
where

import           Syntax.Base
import           Syntax.Kind (Kind)
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Substitution       ( subsAll )
import           Utils                         ( internalError )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S
import           Debug.Trace

type Visited = S.Set T.Type

-- The weak head normal form of a type. Big-step semantics. A total function for
-- well-formed types.
normalise :: TypeDeclMap -> T.Type -> T.Type
normalise td = norm S.empty
  where
    norm :: Visited -> T.Type -> T.Type
    norm visited t
      | isWhnf t = t
      | reappears = T.Skip (getSpan t)
      | otherwise = {- trace ("Norm " ++ show t) $ -} norm insert (reduce td t)
      where
        u = tNameRedex t -- u is Maybe (µ∗U)
        reappears = maybe False   (`S.member` visited) u
        insert    = maybe visited (`S.insert` visited) u

tNameRedex :: T.Type -> Maybe T.Type
tNameRedex = \case 
  t@T.AppTName{}                               -> Just t -- µ∗U
  (T.AppSemi _ t@T.AppTName{} _)               -> Just t -- (µ∗U) ; V
  (T.AppDual _ t@T.AppTName{})                 -> Just t -- Dual (µ∗U)
  (T.AppSemi _ (T.AppDual _ t@T.AppTName{}) _) -> Just t -- (Dual (µ∗U)) ; V
  _                                            -> Nothing

-- Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ t _
    | T.isConstant t && not (T.isSemi t || T.isTName t || T.isDual t) -> True
  -- W-Seq1 _ does not apply, presently; semicolon must be fully applied
  T.App _ T.Semi{} [_] -> True
  -- W-Seq2
  T.AppSemi _ t _ | isWhnf t && not (T.isAppSemi t || T.isSkip t || T.isAppLinChoice t) -> True
  -- W-Var
  T.AppVar{} -> True
  -- W-Abs
  T.Abs{} -> True
  -- W-Dual
  T.AppDual _ T.Var{} -> True
  _ -> False

-- One step type reduction
-- Requires: not (isWhnf t) ?
reduce :: TypeDeclMap -> T.Type -> T.Type
reduce td = \case
  -- 1. Semicolon
  -- R-Neut
  T.AppSemi _ T.Skip{} t -> t
  -- R-Assoc (must come before R.SemiL)
  T.AppSemi s1 (T.AppSemi s2 t1 t2) t3 -> T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
  -- R-Dist (must come before R.SemiL)
  T.AppSemi _ (T.App s t@T.Choice{} us) v -> T.App s t (map (\u -> T.AppSemi (getSpan u) u v) us)
  -- R-SemiL
  T.AppSemi s t u -> T.AppSemi s (reduce td t) u
  -- 2. Duality
  -- R-DSkip
  T.AppDual _ t@T.Skip{} -> t
  -- R-DEnd
  T.AppDual _ t@T.End{}  -> T.dual t
  -- R-DMsg
  T.AppDual _ (T.App s u@T.Message{} ts) -> T.App s (T.dual u) ts
  -- R-DChoice
  T.AppDual s u@T.Choice{} -> T.dual u -- for *& and *+
  T.AppDual s (T.App _ u@T.Choice{} ts) ->  T.App s (T.dual u) (map (T.AppDual s) ts)
  -- R-DQuant
  T.AppDual s1 (T.AppQuant s2 p aks t) -> T.AppQuant s1 (T.dual p) aks (T.AppDual s2 t)
  -- -- R-DDual
  T.AppDual _ (T.AppDual _ t) -> t
  -- R-DDVar - redundant in face of the above; alone seems not enough (normalisation diverges)
  -- T.AppDual s (T.AppDual _ t@T.AppVar{}) -> t
  -- R-DSemi
  T.AppDual s1 (T.AppSemi s2 t1 t2) -> T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
  -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce td t)
  -- 3. R-μ + R-β + TAppL
  -- Q: What if as and ts are of different lengths?
  -- A: Then subsAll considers only the shortest between as and ts
  T.AppTName _ name ts -> case td M.!? name of
    Just (map fst -> as, u) -> subsAll as ts u
    Nothing -> internalError $ "reduce: " ++ show name ++ " type name not in type declaration map, when applied to " ++ show ts
  -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
  -- This last rule must be restricted if we don't want the proviso "Requires:
  -- not (isWhnf t)". Below are only a couple of cases
  -- T.App s t ts | not (T.isDName t || T.isMsg t) -> T.App s (reduce td t) ts
  t -> internalError $ "reduce: non-exhaustive pattern: " ++ show t
