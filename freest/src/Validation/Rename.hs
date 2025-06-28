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
import Validation.Base ( TypeDeclMap )
import Validation.Substitution ( subs, subsAll, unfold )
import Validation.Normalisation ( betaReduces )
import Utils ( internalError )

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | (first s t) is be the smallest variable in set B \ (s union reach t)
first :: Set.Set Variable -> TypeDeclMap -> T.Type -> Variable
first s td t = firstVar var (s `Set.union` reachable td t)
  where var = Variable (Span "<word>" (0,0) (0,0)) "α" defaultInternal

-- | Is a given type absorbing?
absorbing :: TypeDeclMap -> T.Type -> Bool
absorbing td = \case
  T.End{} -> True
  T.Void _ (K.Proper _ _ pk) | pk K.<: K.Session -> True
  T.AppSemi _ t u -> absorbing td t || absorbing td u
  T.SharedChoice{}        -> True -- Unrestricted choice
  T.AppMessage _ K.Un _ _ -> True -- Unrestricted message
  T.App _ T.Choice{} ts -> all (absorbing td) ts
  T.AppDual _ t -> absorbing td t
  -- forall F _ Using instead forall lambda a.T
  T.AppQuant _ _ _ t -> absorbing td t
  -- µ_κ F absorbing if F Void_κ absorbing
  T.TName s name -> case td Map.!? name of
    -- TODO: The kind of T.Void should be that of the 'name', a proper kind
    Just u  -> absorbing td (unfold name (T.Void s (K.uc s)) u)
    Nothing -> internalError $ "absorbing: name " ++ show name ++ " not in type declaration map"
  t -> case betaReduces t of
    Just u -> absorbing td u
    Nothing -> False

-- | The set of free variables reachable in a type.
reachable :: TypeDeclMap -> T.Type -> Set.Set Variable
reachable td = \case
  t | T.isConstant t -> Set.empty
  T.TName{} -> Set.empty
  T.Var _ a -> Set.singleton a
  T.Abs _ (map fst -> as) t -> reachable td t Set.\\ Set.fromList as
  T.AppSemi _ t u | absorbing td t -> reachable td t
                  | otherwise -> reachable td t `Set.union` reachable td u
  T.App _ t us -> Set.unions (map (reachable td) (t:us))


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

