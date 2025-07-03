{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming.

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( reachable
  , first
  , absorbing -- for testing purposes
  , rename
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap, ValidationState, typeDecls, kindSigs, getType, getKind )
import Validation.Substitution ( subs, subsAll )
import Validation.Normalisation ( reduce, betaRule, isWhnf )
import Validation.Kinding ( runSynth' )
import Utils ( internalError )

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Maybe ( isNothing )

-- | (first s t) is be the smallest variable in set B \ (s union reach t)
first :: Set.Set Variable -> TypeDeclMap -> T.Type -> Variable
first s td t = firstVar var (s `Set.union` reachable td t)
  where var = Variable (Span "<word>" (0,0) (0,0)) "α" defaultInternal

  -- | Is a given type absorbing?
absorbing :: ValidationState -> T.Type -> Bool
absorbing vs = \case
  T.End{} -> True
  T.Void _ k | K.isSession k -> True
  T.AppSemi _ t u -> absorbing vs t || absorbing vs u
  T.SharedChoice{}        -> True -- Unrestricted choice
  T.AppMessage _ K.Un _ _ -> True -- Unrestricted message
  T.App _ T.Choice{} ts -> all (absorbing vs) ts
  T.AppDual _ t -> absorbing vs t
  -- forall F _ Using instead forall lambda a.T
  T.AppQuant _ _ _ t -> absorbing vs t
  -- µ_κ F absorbing if F Void_κ absorbing
  t@(T.AppTName s name ts) -> absorbing (vs {typeDecls = Map.insert name (T.Void s k) (typeDecls vs)}) (if null ts then u else T.App s u ts)
    where
      k = getKind vs name
      u = getType vs name
  t -> case betaReduces t of
    Just u -> absorbing vs u
    Nothing -> False

betaReduces :: T.Type -> Maybe T.Type
betaReduces = \case
  -- R-β
  T.App _ t@T.Abs{} us -> Just $ betaRule t us
  -- R-VoidApp
  T.App s (T.Void _ (K.Arrow _ _ k)) [_] -> Just $ T.Void s k
  -- R-TAppL
  T.App s t us -> do
    t' <- betaReduces t
    Just $ T.App s t' us
  _ -> Nothing

-- | The set of free variables reachable in a type.
reachable :: TypeDeclMap -> T.Type -> Set.Set Variable
reachable td t = Set.empty-- \case
  -- t | T.isConstant t -> Set.empty
  -- T.Var _ a -> Set.singleton a
  -- T.Abs _ (map fst -> as) t -> reachable td t Set.\\ Set.fromList as
  -- T.AppSemi _ t u | absorbing td t -> reachable td t
  --                 | otherwise -> reachable td t `Set.union` reachable td u
  -- T.AppDual _ t -> reachable td t
  -- t@(T.App _ u vs) | not (T.isSemi u) && isWhnf t -> Set.unions (map (reachable td) (u:vs)) -- TODO: t /= ;t'
  --                  | isNothing (tNameRedex t) -> reachable td (reduce td t)
  -- -- t@(T.TName s name) -> case td Map.!? name of
  -- --   Just u | absorbing td t -> reachable td (unfold name (T.Void s (K.ls s)) u)
  -- --          | otherwise -> reachable td u
  -- --   Nothing -> internalError $ "reachable: " ++ show name ++ " type name not in type declaration map"
  -- t -> internalError $ "reachable: non-exhaustive pattern: " ++ show t

-- Deprecated

-- | Rename a type.
rename :: TypeDeclMap -> T.Type -> T.Type
rename td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.App s t us -> T.App s (rename td t) (map (rename td) us)
  T.Abs s (unzip -> (as, ks)) t -> 
    T.Abs s (zip bs ks) (rename td (subsAll as (map T.fromVariable bs) t))
    where 
      reach = reachable td t
      bs = foldr (\a bs' -> if a `elem` reach then 
                              firstVar a (Set.fromList bs' `Set.union` reach) : bs'
                            else 
                              nullVar a : bs') 
                 [] as

