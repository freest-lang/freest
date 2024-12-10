{- |
Module      :  Syntax.Substitution
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements capture-avoiding substitution for types, adapted from 
the corrected version of Lennart Augustsson's naïve substitution found in 
[lambda-n-ways repository](https://github.com/sweirich/lambda-n-ways/blob/main/lib/Lennart/Simple.hs).
To be replaced by a more efficient alternative.
-}
module Syntax.Substitution
  ( subs
  , subsAll
  , freeVars
  )
where

import Syntax.Base
import qualified Syntax.Type as T
import qualified Syntax.Kind as K

import Data.Bifunctor (first, second)
import Data.List (intersperse, union, (\\))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

freeVars :: T.Type -> Set.Set Variable
freeVars = \case
    T.Forall _ a k t   -> Set.delete a $ freeVars t
    T.Var _ a          -> Set.singleton a
    T.App _ t ts       -> Set.unions (freeVars t : map freeVars ts)
    T.Choice _ _ _ lts -> Set.unions $ map (freeVars . snd) lts
    _                  -> Set.empty

allVars :: T.Type -> Set.Set Variable
allVars = \case 
    T.Forall _ _ _ t   -> allVars t
    T.Var _ a          -> Set.singleton a
    T.App _ t ts       -> Set.unions (allVars t : map allVars ts)
    T.Choice _ _ _ lts -> Set.unions $ map (allVars . snd) lts
    _                  -> Set.empty

newInternal :: Variable -> Set.Set Variable -> Variable
newInternal a as = a{internal=head ([0..] \\ map internal (Set.toList as))}

subs :: Variable -> T.Type -> T.Type -> T.Type
subs a u = \case 
  t@(T.Forall s b k t')
    | b == a -> t
    | b `Set.member` fvu ->
      T.Forall s b' k (subs b (T.Var (getSpan b') b') t')
    | otherwise -> T.Forall s b k (subs a u t')
    where 
      b' = newInternal b (Set.insert a fvu `Set.union` allVars t')
      fvu = freeVars u
  t@(T.Var _ b)
    | b == a    -> u
    | otherwise -> t
  T.App s f ts -> T.App s (subs a u f) (fmap (subs a u) ts)
  T.Choice s m p lts -> T.Choice s m p (map (second (subs a u)) lts)
  t -> t

subsAll :: [Variable] -> [T.Type] -> T.Type -> T.Type
subsAll as ts u = foldr (uncurry subs) u (zip as ts)
