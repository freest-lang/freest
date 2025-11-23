{- |
Module      :  Syntax.Substitution
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements capture-avoiding substitution for types, adapted from 
the corrected version of Lennart Augustsson's naïve substitution found in 
[lambda-n-ways repository](https://github.com/sweirich/lambda-n-ways/blob/main/lib/Lennart/Simple.hs).
To be replaced by a more efficient alternative.
-}
module Validation.Substitution
  ( subs
  , subsAll
  , freeVars
  )
where

import Syntax.Base
import Syntax.Type qualified as T
import Syntax.Kind qualified as K

import Data.Bifunctor ( first, second )
import Data.List ( intersperse, union )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | The set of free variables ocurring in a type.
freeVars :: T.Type x -> Set.Set Variable
freeVars = \case
    T.Abs _ _ aks t -> freeVars t Set.\\ Set.fromList (map fst aks)
    T.Var _ _ a     -> Set.singleton a
    T.App _ _ t ts  -> Set.unions (freeVars t : map freeVars ts)
    _             -> Set.empty

-- | The set of all variables ocurring in a type.
allVars :: T.Type x -> Set.Set Variable
allVars = \case 
    T.Abs _ _ aks t -> allVars t
    T.Var _ _ a     -> Set.singleton a
    T.App _ _ t ts  -> Set.unions (allVars t : map allVars ts)
    _             -> Set.empty

-- | Type substitution. Substitutes ocurrences of a variable in a type for 
-- another type (usually written @[a -> u] t@).
subs :: Variable -> T.Type x -> T.Type x -> T.Type x
subs a u = \case 
  -- Variables
  t@(T.Var _ _ b)
    | b == a    -> u
    | otherwise -> t
  -- Abstractions (can we do this more elegantly?)
  (T.Abs s x [] t') -> T.Abs s x [] (subs a u t')
  t@(T.Abs s x ((b,k):bks) t')
      | b == a -> t
      | b `Set.member` fvu ->
        let b' = freshVar b (Set.insert a fvu `Set.union` allVars t')
            T.Abs _ _ bks' t'' = subs a u (subs b (T.Var (getSpan b') x b') (T.Abs s x bks t')) -- TODO: BA - check
        in T.Abs s x ((b',k):bks') t''
      | otherwise ->
        let T.Abs _ _ bks' t'' = subs a u (T.Abs s x bks t')
        in T.Abs s x ((b,k):bks') t''
    where  fvu = freeVars u
  -- Applications
  T.App s x f ts -> T.App s x (subs a u f) (fmap (subs a u) ts)
  t -> t

-- Polyadic substituion (written @[as -> us] t@). Considers only the shortest
-- between @as@ and @us@.
subsAll :: [Variable] -> [T.Type x] -> T.Type x -> T.Type x
subsAll as us t = foldr (uncurry subs) t (zip as us)
