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
  (subs
  ,freeVars
  )
where

import Syntax.Base
import qualified Syntax.Type as T
import qualified Syntax.Kind as K

import Data.Bifunctor (first, second)
import Data.List (intersperse, union, (\\))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

freeVars :: T.Type -> Set.Set Variable
-- If forall is just a constant, remove this equation
-- (and make sure there is one for T.Abs)
freeVars (T.Forall _ aks t)   = freeVars t Set.\\ Set.fromList (map fst aks)
freeVars (T.Var _ a)          = Set.singleton a
freeVars (T.Abs _ aks t)      = freeVars t Set.\\ Set.fromList (map fst aks)
freeVars (T.App _ t ts)       = Set.unions (freeVars t : map freeVars ts)
freeVars (T.Labelled _ _ lts) = Set.unions $ map (freeVars . snd) lts
freeVars (T.Tuple _ ts)       = Set.unions $ map freeVars ts
freeVars _                    = Set.empty

allVars :: T.Type -> Set.Set Variable
-- If forall is just a constant, remove this equation
-- (and make sure there is one for T.Abs)
allVars (T.Forall _ aks t)   = allVars t
allVars (T.Var _ a)          = Set.singleton a
allVars (T.Abs _ aks t)      = allVars t
allVars (T.App _ t ts)       = Set.unions (allVars t : map allVars ts)
allVars (T.Labelled _ _ lts) = Set.unions $ map (allVars . snd) lts
allVars (T.Tuple _ ts)       = Set.unions $ map allVars ts
allVars _                    = Set.empty

newInternal :: Variable -> Set.Set Variable -> Variable
newInternal a as = a{internal=head ([0..] \\ map internal (Set.toList as))}

subs :: Variable -> T.Type -> T.Type -> T.Type
subs a u t = sub t
  where
    sub :: T.Type -> T.Type
    -- If forall is just a constant, remove these equations
    -- (and make sure there are some for T.Abs)
    sub t@(T.Forall s ((b,k):bks) t') -- map does not work?
      | b == a = t
      | b `Set.member` fvu = 
        let b' = newInternal b (afvu `Set.union` allVars t')
            T.Forall _ bks' t'' = sub (subs b (T.Var (getSpan b') b') (T.Forall s bks t'))
        in T.Forall s ((b',k):bks') t''
      | otherwise = 
        let T.Forall _ bks' t'' = sub (T.Forall s bks t')
        in T.Forall s ((b,k):bks') t''
    sub t@(T.Var _ b)
      | b == a = u
      | otherwise = t
    sub   (T.Abs s []          t') = T.Abs s [] (sub t')
    sub t@(T.Abs s ((b,k):bks) t') -- map does not work?
      | b == a = t
      | b `Set.member` fvu = 
        let b' = newInternal b (afvu `Set.union` allVars t')
            T.Abs _ bks' t'' = sub (subs b (T.Var (getSpan b') b') (T.Abs s bks t'))
        in T.Abs s ((b',k):bks') t''
      | otherwise = 
        let T.Abs _ bks' t'' = sub (T.Abs s bks t')
        in T.Abs s ((b,k):bks') t''
    sub (T.App s f as) = T.App s (sub f) (map sub as)
    sub (T.Labelled s l lts) = T.Labelled s l (map (second sub) lts)
    sub (T.Tuple s ts) = T.Tuple s (map sub ts)
    sub t = t

    fvu = freeVars u
    afvu = Set.insert a fvu