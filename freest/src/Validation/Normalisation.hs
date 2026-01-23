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

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Substitution ( subsAll )
import Utils ( internalError )

import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Debug.Trace

-- type Visited x = S.Set (T.Type x)

-- | The weak head normal form of a type. Big-step semantics. A total function for
-- well-formed types.
normalise :: TypeDeclMap Kinded -> T.KindedType -> T.KindedType
normalise td = norm S.empty
  where
--    norm :: Visited x -> T.Type x -> T.Type x
    norm visited t
      | isWhnf t = t
      | reappears = T.Void (getSpan t) (T.getExt t) (K.lt $ getSpan t)
      | otherwise = {- trace ("Norm " ++ show t) $ -} norm insert (reduce td t)
      where
        u = tNameRedex t -- u is Maybe (µ∗U)
        reappears = maybe False   (`S.member` visited) u
        insert    = maybe visited (`S.insert` visited) u

-- | Extract the applied @type@ name at the head of a type, if any.
tNameRedex :: T.KindedType -> Maybe T.KindedType
tNameRedex = \case 
  t@T.AppTName{}                               -> Just t -- µ∗U
  (T.AppSemi _ _ t@T.AppTName{} _)               -> Just t -- (µ∗U) ; V
  (T.AppDual _ _ t@T.AppTName{})                 -> Just t -- Dual (µ∗U)
  (T.AppSemi _ _ (T.AppDual _ _ t@T.AppTName{}) _) -> Just t -- (Dual (µ∗U)) ; V
  _                                            -> Nothing

-- | Is a given type a weak head normal form?
isWhnf :: T.KindedType -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ _ t _
    | T.isConstant t && not (T.isSemi t || T.isTName t || T.isDual t) -> True
  -- W-Seq1 _ does not apply, presently; semicolon must be fully applied
  T.App _ _ T.Semi{} [_] -> True
  -- W-Seq2
  T.AppSemi _ _ t _ | isWhnf t && not (T.isAppSemi t || T.isSkip t || T.isAppLinChoice t) -> True
  -- W-Var
  T.AppVar{} -> True
  -- W-Abs
  T.Abs{} -> True
  -- W-Dual
  T.AppDual _ _ T.Var{} -> True
  _ -> False

-- | One step type reduction (requires @not (isWhnf t)@?)
reduce :: TypeDeclMap Kinded -> T.KindedType -> T.KindedType
reduce td = \case
  -- 1. Semicolon
  -- R-Neut
  T.AppSemi _ _ T.Skip{} t -> t
  -- R-Assoc (must come before R.SemiL)
  T.AppSemi s1 x1 (T.AppSemi s2 x2 t1 t2) t3 -> T.AppSemi s1 x1 t1 (T.AppSemi s2 x2 t2 t3)
  -- R-Dist (must come before R.SemiL)
  T.AppSemi _ x1 (T.App s x2 t@T.Choice{} us) v -> T.App s x2 t (map (\u -> T.AppSemi (getSpan u) x1 u v) us)
  -- R-SemiL
  T.AppSemi s x t u -> T.AppSemi s  x(reduce td t) u
  -- 2. Duality
  -- R-DSkip
  T.AppDual _ _ t@T.Skip{} -> t
  -- R-DEnd
  T.AppDual _ _ t@T.End{} -> T.dual t
  -- R-DVoid
  T.AppDual _ _ t@T.Void{} -> t
  -- R-DMsg
  T.AppDual _ _ (T.App s x u@T.Message{} ts) -> T.App s x (T.dual u) ts
  -- R-DChoice
  T.AppDual s _ u@T.Choice{} -> T.dual u -- for *& and *+
  T.AppDual s x1 (T.App _ x2 u@T.Choice{} ts) ->  T.App s x2 (T.dual u) (map (T.AppDual s x1) ts)
  -- R-DQuant
  T.AppDual s1 x1 (T.AppQuant s2 x3 p aks t) -> T.AppQuant s1 x3 (T.dual p) aks (T.AppDual s2 x1 t)
  -- -- R-DDual
  T.AppDual _ _ (T.AppDual _ _ t) -> t
  -- R-DDVar - redundant in face of the above; alone seems not enough (normalisation diverges)
  -- T.AppDual s (T.AppDual _ t@T.AppVar{}) -> t
  -- R-DSemi
  T.AppDual s1 x (T.AppSemi s2 _ t1 t2) -> T.AppSemi s1 x (T.AppDual s1 x t1) (T.AppDual s2 x t2)
  -- R-DCtx
  T.AppDual s x t -> T.AppDual s x (reduce td t)
  -- 3. R-μ + R-β + TAppL
  -- Q: What if as and ts are of different lengths?
  -- A: In that case, subsAll considers only the shortest between as and ts
  T.AppTName s _ _ name ts -> case td M.!? name of
    Just (T.Abs _ _ (map fst -> as) u) -> subsAll as ts u
    Just u -> u
    Nothing -> internalError $ "reduce: " ++ show name ++ " type name not in type declaration map, when applied to " ++ show ts
  -- R-TAppL
  T.App s x t ts -> T.App s x (reduce td t) ts
  -- This last rule must be restricted if we don't want the proviso "Requires:
  -- not (isWhnf t)". Below are only a couple of cases
  -- T.App s t ts | not (T.isDName t || T.isMsg t) -> T.App s (reduce td t) ts
  t -> internalError $ "reduce: non-exhaustive pattern: " ++ show t
