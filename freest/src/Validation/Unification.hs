{- |
Module      :  Validation.Unification
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The unification algorithm from Fig. 14 of the kind-inference paper.

Given a 'Validation.Constraint.Constraints' set, 'unify' computes a
'Validation.KindSubstitution.Substitution' that pins every multiplicity
and prekind metavariable down to a value, or fails when the constraints
are unsatisfiable.

The top-level 'unify' is the calligraphic /U/ from Fig. 14: it iterates
'unifyOne' to a fixed point. The initial substitution maps every
multiplicity variable @φ@ to @1@ (the maximum of the multiplicity
lattice) and every prekind variable @ψ@ to @T@ (the maximum of the
prekind hierarchy). Each iteration tightens the substitution via the
'compose' operation (definition 5 of the paper), which takes the greatest
lower bound point-wise.
-}
module Validation.Unification ( unify ) where

import Syntax.Base
import Syntax.Kind qualified as K
import Validation.Constraint qualified as C
import Validation.KindSubstitution
    ( Substitution(..), emptySubstitution, applyMult, applyPrekind )

import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | The top-level /U/ from Fig. 14: iterate 'unifyOne' to a fixed point.
-- Returns 'Nothing' on a non-unifiable constraint set.
unify :: C.Constraints -> Maybe Substitution
unify cs = loop (initial cs)
  where
    loop σ = do
      σ' <- unifyOne σ (Set.toList cs)
      if σ == σ' then pure σ else loop σ'

-- | The initial substitution: maps every multiplicity variable @φ@ to
-- @1@ ('K.Lin') and every prekind variable @ψ@ to @T@ ('K.Top') — the
-- tops of their respective lattices.
initial :: C.Constraints -> Substitution
initial cs = emptySubstitution
  { multSubs    = Map.fromList [(φ, K.Lin (varSpan φ)) | φ <- Set.toList (multVarsOf cs)]
  , prekindSubs = Map.fromList [(ψ, K.Top)             | ψ <- Set.toList (prekindVarsOf cs)]
  }

-- | The set of multiplicity variables mentioned by a constraint set.
multVarsOf :: C.Constraints -> Set.Set Variable
multVarsOf = foldMap go
  where
    go = \case
      C.SubMult _ m1 m2 -> mvm m1 <> mvm m2
      C.JoinMult _ φ ms -> Set.insert φ (foldMap mvm ms)
      _                 -> Set.empty
    mvm (K.Sup _ lvφs) = Set.fromList (map snd lvφs)
    mvm _              = Set.empty

-- | The set of prekind variables mentioned by a constraint set.
prekindVarsOf :: C.Constraints -> Set.Set Variable
prekindVarsOf = foldMap go
  where
    go = \case
      C.SubPrekind _  p1 p2 -> pkv p1 <> pkv p2
      C.MeetPrekind _ ψ  ps -> Set.insert ψ (foldMap pkv ps)
      C.JoinPrekind _ ψ  ps -> Set.insert ψ (foldMap pkv ps)
      _                     -> Set.empty
    pkv (K.VarPK ψ) = Set.singleton ψ
    pkv _           = Set.empty

-- | Process every constraint once in sequence, tightening σ via 'compose'
-- on the update cases (@φ <: m@, @ψ <: υ@, joins, meets) and checking
-- subkind closure on the check cases (@m <: φ@, @υ <: ψ@, ground).
unifyOne :: Substitution -> [C.Constraint] -> Maybe Substitution
unifyOne σ []           = Just σ
unifyOne σ (c : rest)   = case c of
  C.SubMult _ (K.Sup _ [(_, φ)]) m ->
    unifyOne (updateMult φ (applyMult σ m) σ) rest
  C.SubMult _ m (K.Sup s [(lv, φ)])
    | applyMult σ m K.<: applyMult σ (K.Sup s [(lv, φ)]) -> unifyOne σ rest
    | otherwise                                          -> Nothing
  C.SubMult _ m1 m2
    | applyMult σ m1 K.<: applyMult σ m2 -> unifyOne σ rest
    | otherwise                          -> Nothing
  C.SubPrekind _ (K.VarPK ψ) p ->
    unifyOne (updatePrekind ψ (applyPrekind σ p) σ) rest
  C.SubPrekind _ p (K.VarPK ψ)
    | applyPrekind σ p K.<: applyPrekind σ (K.VarPK ψ) -> unifyOne σ rest
    | otherwise                                        -> Nothing
  C.SubPrekind _ p1 p2
    | applyPrekind σ p1 K.<: applyPrekind σ p2 -> unifyOne σ rest
    | otherwise                                -> Nothing
  C.JoinMult s φ ms ->
    let lub = foldr (K.join . applyMult σ) (K.Sup s []) ms
    in unifyOne (updateMult φ lub σ) rest
  C.JoinPrekind _ ψ ps ->
    let lub = foldr (K.join . applyPrekind σ) K.Top ps
    in unifyOne (updatePrekind ψ lub σ) rest
  C.MeetPrekind _ ψ ps ->
    let glb = foldr (K.meet . applyPrekind σ) K.Top ps
    in unifyOne (updatePrekind ψ glb σ) rest

-- | Update σ at @φ@ by the meet of the new value with the current one,
-- mirroring substitution composition (Definition 5).
updateMult :: Variable -> K.Multiplicity -> Substitution -> Substitution
updateMult φ m σ = σ { multSubs = Map.insertWith meetMult φ m (multSubs σ) }

-- | Update σ at @ψ@ analogously.
updatePrekind :: Variable -> K.Prekind -> Substitution -> Substitution
updatePrekind ψ p σ = σ { prekindSubs = Map.insertWith K.meet ψ p (prekindSubs σ) }

-- | The meet of two multiplicities under the lattice. 'K.Lin' is the top,
-- so meet is the other operand; for two 'K.Sup's the meet is the
-- intersection of their variable lists (the GLB of the join semantics).
meetMult :: K.Multiplicity -> K.Multiplicity -> K.Multiplicity
meetMult (K.Lin _)       m                 = m
meetMult m               (K.Lin _)         = m
meetMult (K.Sup s lvφs1) (K.Sup _ lvφs2)   = K.Sup s (lvφs1 `List.intersect` lvφs2)
