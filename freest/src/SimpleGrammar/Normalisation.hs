{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types

Weak reduction strategies do not reduce under lambda abstractions.
-}

module SimpleGrammar.Normalisation
  ( normalise
  )
where

import           Syntax.Base
import           Syntax.Kind (Kind)
import qualified Syntax.Type                   as T
import           Syntax.Substitution           ( subsAll )
import           Validation.Base               ( TypeDeclMap )

import qualified Data.List.NonEmpty            as NE
import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

-- | The weak head normal form of a type. This function is guaranteed to
-- converge for well-formed types
normalise :: TypeDeclMap -> T.Type -> T.Type
normalise td = norm S.empty
  where
    norm :: S.Set T.Type -> T.Type -> T.Type
    norm visited t
      | isWhnf t = t
      | T.isTName t && t `S.member` visited = T.Skip (getSpan t)
      | T.isTName t = norm (t `S.insert` visited) (reduce td t)
      | otherwise = norm visited (reduce td t)

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ t _
    | T.isConstant t && not (T.isSemi t) && not (T.isTName t) && not (T.isDual t) -> True
  -- W-Seq1 _ does not apply; semicolon must be fully applied
  -- W-Seq2
  T.AppSemi _ t _ | isWhnf t && not (T.isSkip t) && not (T.isSemi t) -> True
  -- W-Var i)
  T.Var{} -> True
  -- W-Var ii)
  T.App _ T.Var{} _ -> True
  -- W-Abs - we do not have abstractions, but we have forall
  T.Forall{} -> True
  -- W-Dual - I think this is the only case for well formed Dual types. TODO: check
  T.AppDual _ T.Var{} -> True
  _ -> False

-- | One step type reduction 
reduce :: TypeDeclMap -> T.Type -> T.Type
reduce td = \case
  -- R-Seq1
  T.AppSemi _ T.Skip{} u -> u
  -- R-Assoc
  T.AppSemi s1 (T.AppSemi s2 t1 t2) t3 ->
    T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
  -- R.Seq2
  T.AppSemi s t u -> -- Redundant: not (T.isAppSemi t)
    T.AppSemi s (reduce td t) u
  -- R-μ + R-β
  T.TName _ id ts -> subsAll as ts u
    where (as, u) = td M.! id
  -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
  -- Duality from here on
  -- R-DSkip
  T.AppDual s T.Skip{} -> T.Skip s
  -- R-DWait, R-DClose
  T.AppDual s (T.End _ p) -> T.End s (T.dual p)
  -- R-D?, R-D!
  T.AppDual s (T.AppMessage _ m p t) ->
    T.AppMessage s m (T.dual p) t
  -- R-D&, – R-D⊕
  T.AppDual s (T.Choice _ m p lts) ->
    T.Choice s m (T.dual p) lts
  -- R-DD _ new rule!
  T.AppDual _ (T.AppDual _ t) -> t
  -- R-D;
  T.AppDual s1 (T.AppSemi s2 t1 t2) ->
    T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
  -- R-DCtx
  T.AppDual s t -> -- Redundant: not (T.isAppSemi t)
    T.AppDual s (reduce td t)

