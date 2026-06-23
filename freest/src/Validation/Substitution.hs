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
  , freeTypeVars
  , subsMultType
  , subsMultMult
  )
where

import Syntax.Base
    ( VarLv(ObjLv), Variable, Located(getSpan), mkFreshVar )
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import Syntax.Kind qualified as K

import Data.Bifunctor ( second)
import Data.List qualified as List
import Data.Set qualified as Set

-- 1. The beta reduction rule

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

-- 2. Type variable substitution

-- | The set of free variables occurring in a type.
freeTypeVars :: T.Type x -> Set.Set Variable
freeTypeVars = \case
  T.Abs _ _ aks t -> freeTypeVars t Set.\\ Set.fromList (map fst aks)
  T.Var _ _ _ a -> Set.singleton a
  T.App _ _ t ts  -> Set.unions (freeTypeVars t : map freeTypeVars ts)
  _               -> Set.empty

-- | The set of all variables ocurring in a type.
allTypeVars :: T.Type x -> Set.Set Variable
allTypeVars = \case 
  T.Abs _ _ aks t -> allTypeVars t
  T.Var _ _ _ a   -> Set.singleton a
  T.App _ _ t ts  -> Set.unions (allTypeVars t : map allTypeVars ts)
  _               -> Set.empty

-- | Type substitution. Substitutes ocurrences of a variable in a type for 
-- another type (usually written @[a -> u] t@).
subs :: Variable -> TK.KindedType -> TK.KindedType -> TK.KindedType
subs a u = \case
  -- Multiplicity quantifier
  TK.ForallM s m [] t' -> TK.ForallM  s m [] (subs a u t')
  TK.ForallM s m (φ : φs) t'
    | φ `Set.member` fmvu ->
      let s = getSpan φ
          φ' = mkFreshVar s (Set.insert φ fmvu `Set.union` allMultVarsType t')
          TK.ForallM _ _ φs' t'' = subs a u (subsMultType ObjLv φ (K.VarM s ObjLv φ') (TK.ForallM s m φs t'))
      in TK.ForallM s m (φ' : φs) t''
    | otherwise ->
      let TK.ForallM _ _ φs' t'' = subs a u (TK.ForallM s m φs t')
      in TK.ForallM s m (φ : φs') t''
    where fmvu = freeMultVars u
  -- Variable
  t@(TK.Var _ _ ObjLv b)
    | b == a    -> u
    | otherwise -> t
  -- Abstraction (can we do this more elegantly?)
  (TK.Abs s [] t') -> TK.Abs s [] (subs a u t')
  t@(TK.Abs s ((b,k):bks) t')
      | b == a -> t
      | b `Set.member` fvu ->
        let b' = mkFreshVar (getSpan b) (Set.insert a fvu `Set.union` allTypeVars t')
            TK.Abs _ bks' t'' = subs a u (subs b (TK.fromVariable ObjLv b' k) (TK.Abs s bks t'))
        in TK.Abs s ((b' , k) : bks') t''
      | otherwise ->
        let TK.Abs _ bks' t'' = subs a u (TK.Abs s bks t')
        in TK.Abs s ((b, k) : bks') t''
    where  fvu = freeTypeVars u
  -- Application
  TK.App s f ts -> TK.smartApp s (subs a u f) (fmap (subs a u) ts)
  t -> t

-- Polyadic substituion (written @[as -> us] t@). Considers only the shortest
-- between @as@ and @us@.
subsAll :: [Variable] -> [TK.KindedType] -> TK.KindedType -> TK.KindedType
subsAll as us t = foldr (uncurry subs) t (zip as us)

-- 3. Multiplicity substitution

subsMultType :: VarLv -> Variable -> K.Multiplicity -> TK.KindedType -> TK.KindedType
subsMultType lv φ m = \case
  TK.Arrow s m' -> 
    TK.Arrow s (subsMultMult lv φ m m')
  TK.AppForall s m' aks t ->
    TK.AppForall s (subsMultMult lv φ m m') (map (second $ subsMultKind lv φ m) aks) (subsMultType lv φ m t)
  TK.AppExists s aks t ->
    TK.AppExists s (map (second $ subsMultKind lv φ m) aks) (subsMultType lv φ m t)
  TK.ForallM s m' [] t -> 
    TK.ForallM s (subsMultMult lv φ m m') [] (subsMultType lv φ m t)
  TK.ForallM s m' (φ' : φs) t
      | lv == ObjLv && φ' == φ -> 
        TK.ForallM s m'' (φ' : φs) t
      | lv == ObjLv && φ' `Set.member` fvm ->
        let φ'' = mkFreshVar (getSpan φ') (Set.insert φ fvm `Set.union` allMultVarsType t)
            TK.ForallM _ _ φs' t' = subsMultType lv φ m (subsMultType lv φ' (K.VarM (getSpan φ'') ObjLv φ'') (TK.ForallM s m'' φs t))
        in TK.ForallM s m'' (φ'' : φs') t'
      | otherwise ->
        let TK.ForallM _ _ φs' t' = subsMultType lv φ m (TK.ForallM s m'' φs t)
        in TK.ForallM s m'' (φ' : φs') t'
    where
      m'' = subsMultMult lv φ m m'
      fvm = allMultVarsMult m
  TK.Void s k -> TK.Void s (subsMultKind lv φ m k)
  TK.Var s k lv' a -> TK.Var s (subsMultKind lv φ m k) lv' a
  -- T.Message s k m p
  TK.Abs s aks t -> TK.Abs s (map (second $ subsMultKind lv φ m) aks) (subsMultType lv φ m t)
  TK.App s t ts  -> TK.App s (subsMultType lv φ m t) (map (subsMultType lv φ m) ts)
  t -> t

subsMultKind :: VarLv -> Variable -> K.Multiplicity -> K.Kind -> K.Kind
subsMultKind lv φ m = \case
  K.Proper s m' pk -> K.Proper s (subsMultMult lv φ m m') pk
  K.Arrow s k1 k2  -> K.Arrow s (subsMultKind lv φ m k1) (subsMultKind lv φ m k2)
  K.Var s τ        -> K.Var s τ

subsMultMult :: VarLv -> Variable -> K.Multiplicity -> K.Multiplicity -> K.Multiplicity
subsMultMult lv φ m = \case
  K.Sup s lvφs | (lv, φ) `elem` lvφs -> -- TODO: better
    K.join m $ K.Sup s $ List.delete (lv, φ) lvφs
  m' -> m'

freeMultVars :: TK.KindedType -> Set.Set Variable
freeMultVars = \case
  TK.Arrow _ m           -> allMultVarsMult m
  TK.AppForall s m aks t -> allMultVarsMult m `Set.union` freeMultVars t
  TK.AppExists s aks t   -> freeMultVars t
  TK.ForallM s m φs t    -> freeMultVars t Set.\\ Set.fromList φs
  TK.Void _ k            -> allMultVarsKind k
  TK.Var _ k _ _         -> allMultVarsKind k
  TK.Abs s aks t         -> freeMultVars t
  TK.App s t ts          -> Set.unions (freeMultVars t : map freeMultVars ts)
  _                      -> Set.empty

allMultVarsType :: TK.KindedType -> Set.Set Variable
allMultVarsType = \case
  TK.Arrow _ m        -> allMultVarsMult m
  T.Quant _ _ _ _ m   -> allMultVarsMult m
  T.ForallM _ _ m _ t -> allMultVarsMult m `Set.union` allMultVarsType t
  TK.Void _ k         -> allMultVarsKind k
  TK.Var _ k _ _      -> allMultVarsKind k
  TK.Abs _ aks t      -> Set.unions (map (allMultVarsKind . snd) aks) `Set.union` allMultVarsType t
  TK.App _ t ts       -> allMultVarsType t `Set.union` Set.unions (map allMultVarsType ts)
  _                   -> Set.empty

allMultVarsKind :: K.Kind -> Set.Set Variable
allMultVarsKind = \case
  K.Proper _ m _  -> allMultVarsMult m
  K.Arrow _ k1 k2 -> allMultVarsKind k1 `Set.union` allMultVarsKind k2
  _               -> Set.empty
  
allMultVarsMult :: K.Multiplicity -> Set.Set Variable
allMultVarsMult = \case
  K.Sup _ lvφs -> Set.fromList $ map snd lvφs
  _            -> Set.empty