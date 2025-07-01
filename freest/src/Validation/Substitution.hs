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
  , unfold
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
freeVars :: T.Type -> Set.Set Variable
freeVars = \case
    T.Abs _ aks t -> freeVars t Set.\\ Set.fromList (map fst aks)
    T.Var _ a     -> Set.singleton a
    T.App _ t ts  -> Set.unions (freeVars t : map freeVars ts)
    _             -> Set.empty

-- | The set of all variables ocurring in a type.
allVars :: T.Type -> Set.Set Variable
allVars = \case 
    T.Abs _ aks t -> allVars t
    T.Var _ a     -> Set.singleton a
    T.App _ t ts  -> Set.unions (allVars t : map allVars ts)
    _             -> Set.empty

-- | Type substitution. Substitutes ocurrences of a variable in a type for 
-- another type (usually written @[a -> u] t@).
subs :: Variable -> T.Type -> T.Type -> T.Type
subs a u = \case 
  -- Variables
  t@(T.Var _ b)
    | b == a    -> u
    | otherwise -> t
  -- Abstractions (can we do this more elegantly?)
  (T.Abs s [] t') -> T.Abs s [] (subs a u t')
  t@(T.Abs s ((b,k):bks) t')
      | b == a -> t
      | b `Set.member` fvu ->
        let b' = freshVar b (Set.insert a fvu `Set.union` allVars t')
            T.Abs _ bks' t'' = subs a u (subs b (T.Var (getSpan b') b') (T.Abs s bks t'))
        in T.Abs s ((b',k):bks') t''
      | otherwise ->
        let T.Abs _ bks' t'' = subs a u (T.Abs s bks t')
        in T.Abs s ((b,k):bks') t''
    where  fvu = freeVars u
  -- Applications
  T.App s f ts -> T.App s (subs a u f) (fmap (subs a u) ts)
  t -> t

-- Polyadic substituion (written @[as -> us] t@). Considers only the shortest
-- between @as@ and @us@.
subsAll :: [Variable] -> [T.Type] -> T.Type -> T.Type
subsAll as us t = foldr (uncurry subs) t (zip as us)

-- | Replace a given name by a type in a type. Usually written @[a -> u] t@. A
-- substitution, only that @a@ is an identifier rather than a variable.
unfold :: Identifier -> T.Type -> T.Type -> T.Type
unfold name t = \case
  T.Abs s aks u -> T.Abs s aks (unfold name t u)
  T.App s u vs -> T.App s (unfold name t u) (map (unfold name t) vs)
  T.TName _ name' | name == name' -> t
  u -> u

