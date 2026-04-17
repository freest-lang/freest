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
  , betaRule
  , freeVars
  )
where

import Syntax.Base
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import Syntax.Kind qualified as K
import Data.Set qualified as Set

-- | The set of free variables occurring in a type.
freeVars :: T.Type x -> Set.Set Variable
freeVars = \case
    T.Abs _ _ aks t -> freeVars t Set.\\ Set.fromList (map fst aks)
    T.Var _ _ _ a -> Set.singleton a
    T.App _ _ t ts  -> Set.unions (freeVars t : map freeVars ts)
    _               -> Set.empty

-- | The set of all variables ocurring in a type.
allVars :: T.Type x -> Set.Set Variable
allVars = \case 
    T.Abs _ _ aks t -> allVars t
    T.Var _ _ _ a -> Set.singleton a
    T.App _ _ t ts  -> Set.unions (allVars t : map allVars ts)
    _               -> Set.empty

-- | Type substitution. Substitutes ocurrences of a variable in a type for 
-- another type (usually written @[a -> u] t@).
subs :: Variable -> TK.KindedType -> TK.KindedType -> TK.KindedType
subs a u = \case 
  -- Variables
  t@(TK.Var _ _ _ b)
    | b == a    -> u
    | otherwise -> t
  -- Abstractions (can we do this more elegantly?)
  (TK.Abs s [] t') -> TK.Abs s [] (subs a u t')
  t@(TK.Abs s ((b,k):bks) t')
      | b == a -> t
      | b `Set.member` fvu ->
        let b' = mkFreshVar (getSpan b) (Set.insert a fvu `Set.union` allVars t')
            TK.Abs _ bks' t'' = subs a u (subs b (TK.fromVariable ObjLv b' k) (TK.Abs s bks t'))
        in TK.Abs s ((b',k):bks') t''
      | otherwise ->
        let TK.Abs _ bks' t'' = subs a u (TK.Abs s bks t')
        in TK.Abs s ((b,k):bks') t''
    where  fvu = freeVars u
  -- Applications
  TK.App s f ts -> TK.smartApp s (subs a u f) (fmap (subs a u) ts)
  t -> t

-- Polyadic substituion (written @[as -> us] t@). Considers only the shortest
-- between @as@ and @us@.
subsAll :: [Variable] -> [TK.KindedType] -> TK.KindedType -> TK.KindedType
subsAll as us t = foldr (uncurry subs) t (zip as us)

-- | Type application, the beta rule.
-- (λα1...αn. T) U1 ... Um -->β
--     T[U1/α1]...[Un/αn]                  if n = m
--     (T[U1/α1]...[Un/αn]) Un+1 ... Um    if m > n
--     λαn+1...αm. T[U1/α1]...[Un/αn]      if n > m
betaRule :: TK.KindedType -> [TK.KindedType] -> TK.KindedType
betaRule (TK.Abs s aks t) us
  | n == m    = v
  | m > n     = TK.App s v (drop n us)
  | otherwise = TK.Abs s (drop m aks) v
  where n = length aks
        m = length us
        v = subsAll (map fst aks) us t
