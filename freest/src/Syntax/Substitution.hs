-- | This module implements capture-avoiding substitution, adapted from the
-- corrected, naïve version of Lennart's substitution found in lambda-n-ways 
-- repository:
-- https://github.com/sweirich/lambda-n-ways/blob/main/lib/Lennart/Simple.hs.
-- To be replaced by a more efficient alternative.

module Syntax.Substitution where

import Syntax.Base
import qualified Syntax.Type as T
import qualified Syntax.Kind as K

import Data.Bifunctor (first, second)
import Data.List (intersperse, union, (\\))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

freeVars :: T.Type -> Set.Set Variable
freeVars (T.Var _ a) = Set.singleton a
freeVars (T.Abs _ aks t) = freeVars t Set.\\ Set.fromList (map fst aks)
freeVars (T.App _ t ts) = Set.unions (freeVars t : map freeVars ts)
freeVars (T.Labelled _ _ lts) = Set.unions $ map (freeVars . snd) lts
freeVars (T.Tuple _ ts) = Set.unions $ map freeVars ts
freeVars _ = Set.empty

allVars :: T.Type -> Set.Set Variable
allVars (T.Var _ a) = Set.singleton a
allVars (T.Abs _ aks t) = allVars t
allVars (T.App _ t ts) = Set.unions (allVars t : map allVars ts)
allVars (T.Labelled _ _ lts) = Set.unions $ map (allVars . snd) lts
allVars (T.Tuple _ ts) = Set.unions $ map allVars ts
allVars _ = Set.empty

newInternal :: Variable -> Set.Set Variable -> Variable
newInternal a as = a{internal=head ([0 ..] \\ map internal (Set.toList as))}


subst :: Variable -> T.Type -> T.Type -> T.Type
subst x s t = sub t -- metavars for type vars are a, b, c; those for types are t, u, v
  where
    sub :: T.Type -> T.Type
    sub t@(T.Var _ v)
      | v == x = s
      | otherwise = t
    sub t@(T.Abs span [] t') = T.Abs span [] (sub t') -- t@ really needed?
    sub t@(T.Abs span vks@((v,k):vks') t') -- map does not work?
      | v == x = T.Abs span vks t' -- v == x = t ?
      | v `Set.member` fvs = 
        let v' = newInternal v (vs `Set.union` allVars t')
            T.Abs _ vks'' t'' = sub (subst v (T.Var (getSpan v') v') (T.Abs span vks' t'))
        in T.Abs span ((v',k):vks'') t''
      | otherwise = 
        let T.Abs _ vks'' t'' = sub (T.Abs span vks' t')
        in T.Abs span ((v,k):vks'') t''
    sub (T.App span f as) = T.App span (sub f) (map sub as)
    sub (T.Labelled span l lts) = T.Labelled span l (map (second sub) lts)
    sub (T.Tuple span ts) = T.Tuple span (map sub ts)
    sub t = t

    fvs = freeVars s
    vs = Set.insert x fvs