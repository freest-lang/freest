{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types
-}

module SimpleGrammar.Normalisation
  ( whReduction
  )
where

import           Syntax.Base
import           Syntax.Kind (Kind)
import qualified Syntax.Type                   as T
import           Syntax.Substitution

import qualified Data.List.NonEmpty            as NE
import qualified Data.Map.Strict               as M

type Lambda t = ([(Variable, Kind)], t)
type TypeDecl = M.Map Identifier (Lambda T.Type)
type ConsDecl = M.Map Identifier [T.Type]
type DataDecl = M.Map Identifier (Lambda [ConsDecl])

-- | The weak head normal form of a type. This function is guaranteed to
-- converge only for well-formed types
whReduction :: TypeDecl -> T.Type -> T.Type
whReduction td t | isWhnf t = t
                 | otherwise = whReduction td (reduce td t)

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ t _
    | T.isConstant t 
    && not (T.isSemi  t) 
    && not (T.isDual  t) -> True
  -- W-Seq1 _ does not apply; semicolon must be fully applied
  -- W-Seq2
  T.AppSemi _ t _ | not (T.isSkip t) && not (T.isSemi t) -> True
  -- W-Var (i)
  T.Var{} -> True
  -- W-Var (ii)
  T.App _ T.Var{} _ -> True
  -- W-Abs - we do not have abstractions, but we have forall
  T.Forall{} -> True
  -- W-Dual - I think this is the only case for well formed Dual types
  T.AppDual _ T.Var{} -> True
  _ -> False

-- | One step type reduction
reduce :: TypeDecl -> T.Type -> T.Type
reduce td = \case
  -- R-Seq1
  T.AppSemi _ T.Skip{} u -> u
  -- R.Seq2
  T.AppSemi s t u | not (T.isAppSemi t) ->
    T.AppSemi s (reduce td t) u
  -- R-Assoc
  T.AppSemi s1 (T.AppSemi s2 t1 t2) t3 ->
    T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
  -- R-μ
  T.TName _ id ts -> rBeta (map fst vks) ts u
    where
      (vks, u) = td M.! id
      rBeta :: [Variable] -> [T.Type] -> T.Type -> T.Type
      -- TODO: assuming vs and ts of the same length
      rBeta vs ts u = foldr (uncurry subs) u (zip vs ts)
  -- R-β - No such thing
  -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
  -- R-D;
  T.AppDual s1 (T.AppSemi s2 t1 t2) ->
    T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
  -- R-DSkip
  T.AppDual s T.Skip{} -> T.Skip s
  -- R-DEnd
  T.AppDual s (T.End _ p) -> T.End s (T.dual p)
  -- R-D?, R-D!
  T.AppDual s (T.AppMessage _ m p t) ->
    T.AppMessage s m (T.dual p) t
  -- R-D&, – R-D⊕
  T.AppDual s (T.Choice _ m p lts) ->
    T.Choice s m (T.dual p) lts
  -- R-DDVar
  T.AppDual _ (T.AppDual _ t@T.Var{}) -> t
  -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce td t)

