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
import Validation.Substitution ( subs, subsAll )
import Utils ( internalError )

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

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

-- | (first s t) is be the smallest variable in set B \ (s union reach t)
first :: Set.Set Variable -> TypeDeclMap -> T.Type -> Variable
first s td t = firstVar var (s `Set.union` reachable td t)
  where var = Variable (Span "<word>" (0,0) (0,0)) "α" defaultInternal

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

-- | Is a type absorbing?
absorbing :: TypeDeclMap -> T.Type -> Bool
absorbing td = \case
  T.End{} -> True
  T.Void{} -> True
  T.SharedChoice{} -> True -- Unrestricted choice
  T.AppMessage _ K.Un _ _ -> True -- Unrestricted message
  T.AppSemi _ t u -> absorbing td t || absorbing td u
  T.App _ T.Choice{} ts -> all (absorbing td) ts
  T.AppDual _ t -> absorbing td t
  -- forall F _ Using isnatead forall lambda a.T
  T.AppQuant _ _ _ t -> absorbing td t
  T.AppTName _ id ts -> case td Map.!? id of
    Just u  -> absorbing td u
    Nothing -> internalError $ "absorbing: " ++ show id ++ " name not in type declaration map, when applied to " ++ show ts
  
  _ -> False
