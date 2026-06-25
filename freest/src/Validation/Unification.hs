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
    ( Substitution(..), emptySubstitution, applyMult, applyPrekind, applyKind )

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
      C.SeqMult _ φ m1 m2 _ -> Set.insert φ (mvm m1 <> mvm m2)
      C.KindEq _ k1 k2  -> kmv k1 <> kmv k2
      _                 -> Set.empty
    mvm (K.Sup _ lvφs) = Set.fromList (map snd lvφs)
    mvm _              = Set.empty
    -- Multiplicity variables embedded in a 'KindEq' kind (e.g. the fresh
    -- @φ@ a promotion introduces via @κ = Proper φ ψ@): collect them so the
    -- initial substitution gives each a default, rather than leaving a raw
    -- 'K.Sup' var that 'applyMult' can't resolve.
    kmv = \case
      K.Proper _ m _ -> mvm m
      K.Arrow _ a b  -> kmv a <> kmv b
      K.Var{}        -> Set.empty

-- | The set of prekind variables mentioned by a constraint set.
prekindVarsOf :: C.Constraints -> Set.Set Variable
prekindVarsOf = foldMap go
  where
    go = \case
      C.SubPrekind _  p1 p2 -> pkv p1 <> pkv p2
      C.MeetPrekind _ ψ  ps -> Set.insert ψ (foldMap pkv ps)
      C.JoinPrekind _ ψ  ps -> Set.insert ψ (foldMap pkv ps)
      C.SeqMult _ _ _ _ v   -> pkv v
      C.KindEq _ k1 k2      -> kpv k1 <> kpv k2
      _                     -> Set.empty
    pkv (K.VarPK ψ) = Set.singleton ψ
    pkv _           = Set.empty
    -- Prekind variables embedded in a 'KindEq' kind (the fresh @ψ@ from a
    -- @κ = Proper φ ψ@ promotion): collect so they default to @T@ instead of
    -- surviving as a raw 'K.VarPK' that 'K.meet' then chokes on.
    kpv = \case
      K.Proper _ _ pk -> pkv pk
      K.Arrow _ a b   -> kpv a <> kpv b
      K.Var{}         -> Set.empty

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
  -- CK-Seq result multiplicity: @φ = if υ₁ = C then m₁ else m₁ ⊔ m₂@.
  -- As the fixpoint drives υ₁ down toward 'K.Channel', the right-hand side
  -- only decreases (since @m₁ <: m₁⊔m₂@), so 'updateMult' (a meet/GLB) lands
  -- on the correct value regardless of iteration order.
  C.SeqMult _ φ m1 m2 pk1 ->
    let m = if applyPrekind σ pk1 == K.Channel
              then applyMult σ m1
              else K.join (applyMult σ m1) (applyMult σ m2)
    in unifyOne (updateMult φ m σ) rest
  C.JoinPrekind _ ψ ps ->
    let lub = foldr (K.join . applyPrekind σ) K.Top ps
    in unifyOne (updatePrekind ψ lub σ) rest
  C.MeetPrekind _ ψ ps ->
    let glb = foldr (K.meet . applyPrekind σ) K.Top ps
    in unifyOne (updatePrekind ψ glb σ) rest
  C.KindEq s k1 k2 -> case (chaseShape σ k1, chaseShape σ k2) of
    -- Decompose 'Arrow' structurally.
    (K.Arrow _ a1 b1, K.Arrow _ a2 b2) ->
      unifyOne σ (C.KindEq s a1 a2 : C.KindEq s b1 b2 : rest)
    -- Var = Var of the same identity: already equal, nothing to do.
    (K.Var _ τ1, K.Var _ τ2) | τ1 == τ2 -> unifyOne σ rest
    -- Var on either side: bind in 'kindSubs' (with an occurs check).
    (K.Var _ τ, k)
      | occursIn τ k -> Nothing
      | otherwise    -> unifyOne (updateKind τ k σ) rest
    (k, K.Var _ τ)
      | occursIn τ k -> Nothing
      | otherwise    -> unifyOne (updateKind τ k σ) rest
    -- Leaf 'Proper' = 'Proper': two-way 'SubMult'/'SubPrekind'.
    (K.Proper _ m1 pk1, K.Proper _ m2 pk2) ->
      unifyOne σ ( C.SubMult    s m1  m2
                 : C.SubMult    s m2  m1
                 : C.SubPrekind s pk1 pk2
                 : C.SubPrekind s pk2 pk1
                 : rest )
    -- Shape mismatch (e.g. 'Arrow' vs 'Proper'): unsolvable.
    _ -> Nothing

-- | Update σ at @τ@ by binding the kind variable to the given kind. The
-- value is assumed to already have been 'applyKind'-ed by σ at the call
-- site, so the resulting substitution is idempotent for @τ@.
updateKind :: Variable -> K.Kind -> Substitution -> Substitution
updateKind τ k σ = σ { kindSubs = Map.insert τ k (kindSubs σ) }

-- | Resolve a kind's whole-kind metavariables — chasing @kindSubs@ to a
-- fixpoint, with a visited-set cycle guard — but leave multiplicity and prekind
-- variables /intact/. Used to decompose a 'C.KindEq': the leaf @Proper@s must
-- keep their @φ@/@ψ@ variables so the resulting two-way 'C.SubMult'/'C.SubPrekind'
-- constraints can still /lower/ them. Using 'applyKind' here instead would
-- freeze each such variable at its default (e.g. @φ ↦ 1@) before the equality
-- has a chance to constrain it, turning a satisfiable equation into an
-- unsatisfiable ground check like @1 <: *@.
chaseShape :: Substitution -> K.Kind -> K.Kind
chaseShape σ = go Set.empty
  where
    go seen = \case
      k@(K.Var _ τ)
        | τ `Set.member` seen -> k
        | otherwise           ->
            maybe k (go (Set.insert τ seen)) (Map.lookup τ (kindSubs σ))
      K.Arrow s k1 k2 -> K.Arrow s (go seen k1) (go seen k2)
      k@K.Proper{}    -> k

-- | Occurs check: does the kind variable @τ@ appear anywhere in @k@?
occursIn :: Variable -> K.Kind -> Bool
occursIn τ = \case
  K.Var _ τ'      -> τ == τ'
  K.Arrow _ k1 k2 -> occursIn τ k1 || occursIn τ k2
  K.Proper{}      -> False

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
