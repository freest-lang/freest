{- |
Module      :  Validation.KindSubstitution
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

A 'Substitution' carries the solution produced by
'Validation.Unification.unify': maps from kind, multiplicity and prekind
metavariables to their resolved values. This module also provides:

  * single-variable kind substitution ('subs');
  * point-wise application of a 'Substitution' to a multiplicity, prekind
    or kind ('applyMult', 'applyPrekind', 'applyKind');
  * a phase-polymorphic 'applyType' walker that recurses into every
    embedded mult / prekind / kind annotation;
  * 'applyModule', which thaws every kind annotation in a scoped module
    (kind signatures, type-decl bodies, datatype parameter kinds, and
    constructor field types).
-}
module Validation.KindSubstitution
  ( Substitution(..)
  , emptySubstitution
  , subs
  , applyMult
  , applyPrekind
  , applyKind
  , applyType
  , applyKindedType
  , applyModule
  , applyKindedModule
  ) where

import Syntax.Base
import Syntax.Declarations qualified as D
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded () -- for the @XType Kinded = K.Kind@ instance

import Data.Bifunctor ( second )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | A substitution maps each kind of metavariable that can appear in a
-- 'K.Kind' to its resolved value:
--
--     * 'kindSubs'   — @K.Var τ@ ↦ 'K.Kind'
--     * 'multSubs'   — multiplicity variables (the @φ@ inside @K.Sup@) ↦ 'K.Multiplicity'
--     * 'prekindSubs' — prekind variables (the @ψ@ inside @K.VarPK@) ↦ 'K.Prekind'
--
-- 'Validation.Unification.unify' produces the @multSubs@ and @prekindSubs@
-- maps; the @kindSubs@ map is for a downstream pass that pins whole-kind
-- metavariables to their solved shape (e.g. @τ ↦ Proper m^φ ψ@).
data Substitution = Substitution
  { kindSubs    :: Map.Map Variable K.Kind
  , multSubs    :: Map.Map Variable K.Multiplicity
  , prekindSubs :: Map.Map Variable K.Prekind
  } deriving (Eq, Show)

emptySubstitution :: Substitution
emptySubstitution = Substitution Map.empty Map.empty Map.empty

-- | Single-variable kind substitution. @subs τ u k@ replaces every
-- @K.Var _ τ@ in @k@ by @u@.
subs :: Variable -> K.Kind -> K.Kind -> K.Kind
subs τ u = \case
  k@(K.Var _ τ')
    | τ' == τ   -> u
    | otherwise -> k
  K.Arrow s k1 k2 -> K.Arrow s (subs τ u k1) (subs τ u k2)
  k@K.Proper{}    -> k

-- | Apply a substitution to a multiplicity, substituting every bound
-- variable. Free variables (none in σ) are kept as-is.
applyMult :: Substitution -> K.Multiplicity -> K.Multiplicity
applyMult σ = \case
  m@K.Lin{}    -> m
  K.Sup s lvφs -> foldr K.join (K.Sup s [])
    (map (\(lv, φ) -> Map.findWithDefault (K.Sup s [(lv, φ)]) φ (multSubs σ)) lvφs)

-- | Apply a substitution to a prekind. Free variables are kept as-is.
applyPrekind :: Substitution -> K.Prekind -> K.Prekind
applyPrekind σ = \case
  K.VarPK ψ -> Map.findWithDefault (K.VarPK ψ) ψ (prekindSubs σ)
  pk        -> pk

-- | Apply a substitution to a kind. Descends into 'K.Proper' and 'K.Arrow';
-- substitutes whole-kind metavariables via @kindSubs@. A @kindSubs@ binding may
-- itself mention further metavariables (e.g. @κ ↦ κ₀ -> κ₁@ with @κ₀ ↦ 1T@), so
-- the 'K.Var' case re-applies the substitution to the looked-up kind, composing
-- the chain to a fixpoint. The visited set breaks any (ill-formed) cycle,
-- leaving the offending variable unresolved rather than looping.
applyKind :: Substitution -> K.Kind -> K.Kind
applyKind σ = go Set.empty
  where
    go seen = \case
      k@(K.Var _ τ)
        | τ `Set.member` seen -> k
        | otherwise           ->
            maybe k (go (Set.insert τ seen)) (Map.lookup τ (kindSubs σ))
      K.Proper s m pk -> K.Proper s (applyMult σ m) (applyPrekind σ pk)
      K.Arrow s k1 k2 -> K.Arrow s (go seen k1) (go seen k2)

-- | Apply a substitution to a 'Scoped' type, descending into every embedded
-- 'K.Multiplicity', 'K.Prekind' and 'K.Kind' annotation. The @XType Scoped@
-- slot is 'Void' and is passed through unchanged.
applyType :: Substitution -> T.Type x -> T.Type x
applyType σ = \case
  T.Int s x                 -> T.Int s x
  T.Float s x               -> T.Float s x
  T.Char s x                -> T.Char s x
  T.Arrow s x m             -> T.Arrow s x (applyMult σ m)
  T.Quant s x p pk m        -> T.Quant s x p (applyPrekind σ pk) (applyMult σ m)
  T.ForallM s x m φs t      -> T.ForallM s x (applyMult σ m) φs (applyType σ t)
  T.Void s x k              -> T.Void s x (applyKind σ k)
  T.Skip s x                -> T.Skip s x
  T.End s x p               -> T.End s x p
  T.Message s x m p         -> T.Message s x (applyMult σ m) p
  T.Choice s x m p ls       -> T.Choice s x (applyMult σ m) p ls
  T.Semi s x                -> T.Semi s x
  T.Dual s x                -> T.Dual s x
  T.TName s x i             -> T.TName s x i
  T.DName s x i             -> T.DName s x i
  T.Var s x lv a            -> T.Var s x lv a
  T.Abs s x aks t           -> T.Abs s x (map (second (applyKind σ)) aks) (applyType σ t)
  T.App s x t ts            -> T.App s x (applyType σ t) (map (applyType σ) ts)

-- | Apply a substitution to a 'Kinded' type. Like 'applyType', but also
-- substitutes the embedded @K.Kind@ annotation (the @XType Kinded@ slot) on
-- every node, so that residual kind metavariables introduced by CT-App and
-- bound in 'kindSubs' are rewritten to their solved value.
applyKindedType :: Substitution -> T.Type Kinded -> T.Type Kinded
applyKindedType σ = walk
  where
    k = applyKind σ
    walk = \case
      T.Int s x                 -> T.Int s (k x)
      T.Float s x               -> T.Float s (k x)
      T.Char s x                -> T.Char s (k x)
      T.Arrow s x m             -> T.Arrow s (k x) (applyMult σ m)
      T.Quant s x p pk m        -> T.Quant s (k x) p (applyPrekind σ pk) (applyMult σ m)
      T.ForallM s x m φs t      -> T.ForallM s (k x) (applyMult σ m) φs (walk t)
      T.Void s x kd             -> T.Void s (k x) (k kd)
      T.Skip s x                -> T.Skip s (k x)
      T.End s x p               -> T.End s (k x) p
      T.Message s x m p         -> T.Message s (k x) (applyMult σ m) p
      T.Choice s x m p ls       -> T.Choice s (k x) (applyMult σ m) p ls
      T.Semi s x                -> T.Semi s (k x)
      T.Dual s x                -> T.Dual s (k x)
      T.TName s x i             -> T.TName s (k x) i
      T.DName s x i             -> T.DName s (k x) i
      T.Var s x lv a            -> T.Var s (k x) lv a
      T.Abs s x aks t           -> T.Abs s (k x) (map (second k) aks) (walk t)
      T.App s x t ts            -> T.App s (k x) (walk t) (map walk ts)

-- | Apply a substitution to every kind annotation in a scoped module:
-- kind signatures, type-decl bodies, datatype parameter kinds, and
-- constructor field types. Expression-level annotations inside
-- 'definitions' are left untouched (they hold no metavariables relevant
-- to kind inference at this phase).
applyModule :: Substitution -> M.ScopedModule -> M.ScopedModule
applyModule σ m = m
  { M.kindSigs  = fmap (applyKind σ)             (M.kindSigs  m)
  , M.typeDecls = fmap (second (applyType σ))    (M.typeDecls m)
  , M.dataDecls = applyDataDecls (M.dataDecls m)
  }
  where
    applyDataDecls :: D.DataDecls Scoped -> D.DataDecls Scoped
    applyDataDecls dds = D.DataDecls
      { D.ddCons  = fmap (second (map (applyType σ))) (D.ddCons  dds)
      , D.ddTypes = fmap (\(aks, cs) -> (map (second (applyKind σ)) aks, cs))
                         (D.ddTypes dds)
      }

-- | Apply a substitution to every kind annotation in a kinded module —
-- the same shape as 'applyModule' specialised to the 'Kinded' phase. Uses
-- 'applyKindedType' so the @K.Kind@ stored in each node's @XType@ slot is
-- also rewritten (CT-App leaves residual kind metavariables there).
applyKindedModule :: Substitution -> M.KindedModule -> M.KindedModule
applyKindedModule σ m = m
  { M.kindSigs  = fmap (applyKind σ)                  (M.kindSigs  m)
  , M.typeDecls = fmap (second (applyKindedType σ))   (M.typeDecls m)
  , M.dataDecls = applyDataDecls (M.dataDecls m)
  }
  where
    applyDataDecls :: D.DataDecls Kinded -> D.DataDecls Kinded
    applyDataDecls dds = D.DataDecls
      { D.ddCons  = fmap (second (map (applyKindedType σ))) (D.ddCons  dds)
      , D.ddTypes = fmap (\(aks, cs) -> (map (second (applyKind σ)) aks, cs))
                         (D.ddTypes dds)
      }
