{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types

Weak reduction strategies do not reduce under lambda abstractions.
-}

module Validation.Normalisation
  ( normalise
  , isWhnf
  )
where

import           Syntax.Base
import           Syntax.Kind (Kind)
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Substitution           ( subsAll )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

type Visited = S.Set T.Type

-- | The weak head normal form of a type. This function is guaranteed to
-- converge for well-formed types
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
tNameRedex t@T.AppTName{}                               = Just t -- µ∗U
tNameRedex (T.AppSemi _ t@T.AppTName{} _)               = Just t -- (µ∗U) ; V
tNameRedex (T.AppDual _ t@T.AppTName{})                 = Just t -- Dual (µ∗U)
tNameRedex (T.AppSemi _ (T.AppDual _ t@T.AppTName{}) _) = Just t -- (Dual (µ∗U)) ; V
tNameRedex _                                            = Nothing

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf = \case
  -- W-Const0 i)
  t | T.isConstant t -> True
  -- W-Const0 ii)
  T.Choice{} -> True
  -- W-Const1
  T.App _ t _
    | T.isConstant t && not (T.isSemi t) && not (T.isTName t) && not (T.isDual t) -> True
  -- W-Seq1 _ does not apply; semicolon must be fully applied
  -- W-Seq2
  T.AppSemi _ t _ | isWhnf t && not (T.isSkip t) && not (T.isSemi t) -> True
  -- W-Var
  T.AppVar{} -> True
  -- W-Abs _ we do not have abstractions, but we have forall
  T.Quant{} -> True
  -- W-Dual - I think this is the only case for well formed Dual types. TODO: check
  T.AppDual _ T.Var{} -> True
  _ -> False

-- | One step type reduction 
reduce :: TypeDeclMap -> T.Type -> T.Type
reduce td = \case
  -- R-Neut
  T.AppSemi _ T.Skip{} t -> t
  -- R-Assoc
  T.AppSemi s1 (T.AppSemi s2 t1 t2) t3 -> T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
  -- R.Seq
  T.AppSemi s t u -> T.AppSemi s (reduce td t) u
  -- R-μ + R-β
  -- Q: What if as and ts are of different lengths?
  -- A: Should not happen with well-formed types
  T.AppTName _ id ts -> subsAll as ts u
    where (as, u) = td M.! id
  -- Duality from here on
  -- R-DSkip
  T.AppDual s T.Skip{} -> T.Skip s
  -- R-DWait, R-DClose
  T.AppDual s (T.End _ p) -> T.End s (T.dual p)
  -- R-D?, R-D!
  T.AppDual s (T.AppMessage _ m p t) -> T.AppMessage s m (T.dual p) t
  -- R-D&, – R-D⊕
  T.AppDual s (T.Choice _ m p lts) -> T.Choice s m (T.dual p) lts
  -- R-DDual
  T.AppDual _ (T.AppDual _ t) -> t
  -- R-D;
  T.AppDual s1 (T.AppSemi s2 t1 t2) -> T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
  -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce td t)
  -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
  t -> error $ "reduce " ++ show t
