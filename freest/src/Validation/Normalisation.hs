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

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

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
      | otherwise = norm insert (reduce td t)
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
    | T.isConstant t && not (T.isSemi t || T.isTName t || T.isDual t || T.isChoice t) -> True
  -- W-Const1
  T.Choice{} -> True
  -- W-Seq1 _ does not apply; semicolon must be fully applied
  -- W-Seq2
  T.AppSemi _ t _ | isWhnf t && not (T.isAppSemi t || T.isSkip t {-|| T.isChoice t-}) -> True
  -- W-Var
  T.AppVar{} -> True
  -- W-Abs _ we do not have abstractions, but we have quantifiers
  T.Quant{} -> True
  -- W-Dual - I think this is the only case for well formed Dual types.
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
  -- R-Dist
  -- T.AppSemi s (T.Choice s' m p idts) u -> T.Choice s m p (map (\(id, t) -> (id, T.AppSemi s' t u)) idts)
  -- R-SemiL
  T.AppSemi s t u -> T.AppSemi s (reduce td t) u
  -- 2. Duality
  -- R-DSkip
  T.AppDual _ t@T.Skip{} -> t
  -- R-DEnd
  T.AppDual s (T.End _ p) -> T.End s (T.dual p)
  -- R-DMsg
  T.AppDual s (T.AppMessage _ m p t) -> T.AppMessage s m (T.dual p) t
  -- R-DChoice
  T.AppDual s (T.Choice _ m p lts) -> T.Choice s m (T.dual p) lts
  -- R-DQuant
  T.AppDual s1 (T.Quant s2 p a k t) -> T.Quant s1 (T.dual p) a k (T.AppDual s2 t)
  -- -- R-DDual
  T.AppDual _ (T.AppDual _ t) -> t
  -- R-DDVar - redundant in face of the above; alone seems not enough (something diverges)
  -- T.AppDual s (T.AppDual _ t@T.AppVar{}) -> t
  -- R-DSemi
  T.AppDual s1 (T.AppSemi s2 t1 t2) -> T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
  -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce td t)
  -- 3. R-μ + R-β + TAppL
  -- R-μ + R-β
  -- Q: What if as and ts are of different lengths?
   -- A: Should not happen with well-formed types
  T.AppTName _ name ts -> case td M.!? name of
    Just (as, u) -> subsAll as ts u
    Nothing -> error $ "reduce: " ++ show name ++ " name not in type declaration map, when applied to " ++ show ts
  -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
  -- This last rule must be restricted if we don't want the proviso "Requires:
  -- not (isWhnf t)". Below are only a couple of cases
  -- T.App s t ts | not (T.isDName t || T.isMsg t) -> T.App s (reduce td t) ts
  t -> error $ "reduce: non-exhaustive pattern: " ++ show t
