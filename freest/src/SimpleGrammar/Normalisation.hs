{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types
-}

module SimpleGrammar.Normalisation
  ( whnf
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
whnf :: TypeDecl -> T.Type -> T.Type
whnf td t | isWhnf t = t
          | otherwise = whnf td (reduce td t)

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf = \case
  -- W-Const0
  t | T.isConstant t -> True
  -- W-Const1
  T.App _ t _
    |  T.isConstant   t 
    && not (T.isSemi  t) 
    && not (T.isTName t) -- TODO: t must not be a type reference (datatype name OK)
    && not (T.isDual  t) -> True
  -- W-Seq1 _ does not apply; semicolon must be fully applied
  -- W-Seq2
  T.AppSemi _ t _ | not (T.isSkip t) && not (T.isSemi t) -> True
  -- W-Var
  T.Var{} -> True
  -- W-Var
  T.App _ T.Var{} _ -> True
  -- W-Abs
  T.Forall{} -> True
  -- W-Dual
  T.AppDual _ t -> isWhnf t && isDualArgWhnf t
    where
      isDualArgWhnf :: T.Type -> Bool
      isDualArgWhnf = \case 
        T.Skip{}     -> False
        T.End{}      -> False
        T.Message{}  -> False
        T.AppSemi{}  -> False
        T.Labelled{} -> False
      -- (T.AppDual _ T.Dual{} (T.Var{} NE.:| _)) -> False
        _            -> True
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
  -- R-β _ No such thing
  -- R-TAppL
  T.App s t ts -> T.App s (reduce td t) ts
  -- R-D;
  T.AppDual s1 (T.AppSemi s2 t1 t2) ->
    T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
  -- R-Skip
  T.AppDual s T.Skip{} -> T.Skip s
  -- R-End
  T.AppDual s (T.End _ p) ->  T.End s (T.dual p)
  -- R-D?, R-D!
  T.AppDual s (T.App _ (T.Message a m p) ts) ->
    T.App s (T.Message a m (T.dual p)) ts
  -- R-D&, – R-D⊕
  T.AppDual s (T.Labelled _ (T.Choice m p) idts) ->
    T.Labelled s (T.Choice m (T.dual p)) idts
  -- R-DDVar
  T.AppDual _ (T.AppDual _ t@T.Var{}) -> t
  -- R-DCtx
  T.AppDual s t -> T.AppDual s (reduce td t)

