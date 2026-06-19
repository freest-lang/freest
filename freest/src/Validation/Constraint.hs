{- |
Module      :  Validation.Constraint
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The syntax of constraints generated during kind checking, following the
grammar of Fig. 8 of the paper:

> C ::= m <: m
>     | v <: v
>     | ψ = ⊓_{ℓ∈L} v_ℓ
>     | ψ = ⊔_{ℓ∈L} v_ℓ
>     | φ = ⊔_{ℓ∈L} m_ℓ

where @m@ is a 'Multiplicity', @v@ is a 'Prekind', @φ@ a multiplicity
variable and @ψ@ a prekind variable.

Kind inference for the FreeST programming language
https://doi.org/10.1016/j.jlamp.2025.101083
-}
module Validation.Constraint
  ( Constraint(..)
  , Constraints
  ) where

import Syntax.Base ( Located(..), Span, Variable )
import Syntax.Kind ( Multiplicity, Prekind )

import Data.List qualified as List
import qualified Data.Set as Set

-- | A single constraint generated during kind checking. Each form carries
-- a 'Span' pointing at the source position that produced it.
data Constraint
  = SubMult Span Multiplicity Multiplicity
    -- ^ @m₁ <: m₂@ — multiplicity subtyping.
  | SubPrekind Span Prekind Prekind
    -- ^ @v₁ <: v₂@ — prekind subtyping.
  | MeetPrekind Span Variable [Prekind]
    -- ^ @ψ = ⊓_{ℓ∈L} v_ℓ@ — the prekind variable @ψ@ is the meet of the
    -- given prekinds.
  | JoinPrekind Span Variable [Prekind]
    -- ^ @ψ = ⊔_{ℓ∈L} v_ℓ@ — the prekind variable @ψ@ is the join of the
    -- given prekinds.
  | JoinMult Span Variable [Multiplicity]
    -- ^ @φ = ⊔_{ℓ∈L} m_ℓ@ — the multiplicity variable @φ@ is the join of
    -- the given multiplicities.

-- | A constraint set.
type Constraints = Set.Set Constraint

instance Show Constraint where
  show = \case
    SubMult _ m1 m2    -> show m1 ++ " <: " ++ show m2
    SubPrekind _ v1 v2 -> show v1 ++ " <: " ++ show v2
    MeetPrekind _ ψ vs -> show ψ ++ " = ⊓ {" ++ List.intercalate ", " (map show vs) ++ "}"
    JoinPrekind _ ψ vs -> show ψ ++ " = ⊔ {" ++ List.intercalate ", " (map show vs) ++ "}"
    JoinMult _ φ ms    -> show φ ++ " = ⊔ {" ++ List.intercalate ", " (map show ms) ++ "}"

-- | Span-blind: the source position is metadata, not part of a constraint's
-- identity (so two constraints that differ only in location compare equal).
instance Eq Constraint where
  (==) = \cases
    (SubMult _ m1 m2)     (SubMult _ m1' m2')     -> m1 == m1' && m2 == m2'
    (SubPrekind _ v1 v2)  (SubPrekind _ v1' v2')  -> v1 == v1' && v2 == v2'
    (MeetPrekind _ ψ vs)  (MeetPrekind _ ψ' vs')  -> ψ  == ψ'  && vs == vs'
    (JoinPrekind _ ψ vs)  (JoinPrekind _ ψ' vs')  -> ψ  == ψ'  && vs == vs'
    (JoinMult _ φ ms)     (JoinMult _ φ' ms')     -> φ  == φ'  && ms == ms'
    _                     _                       -> False

-- | Span-blind ordering, by constructor index then by payload. Required for
-- 'Constraints' (a 'Set').
instance Ord Constraint where
  compare = \cases
    (SubMult _ m1 m2)     (SubMult _ m1' m2')     -> compare (m1, m2) (m1', m2')
    (SubPrekind _ v1 v2)  (SubPrekind _ v1' v2')  -> compare (v1, v2) (v1', v2')
    (MeetPrekind _ ψ vs)  (MeetPrekind _ ψ' vs')  -> compare (ψ, vs)  (ψ',  vs')
    (JoinPrekind _ ψ vs)  (JoinPrekind _ ψ' vs')  -> compare (ψ, vs)  (ψ',  vs')
    (JoinMult _ φ ms)     (JoinMult _ φ' ms')     -> compare (φ, ms)  (φ',  ms')
    c1                    c2                      -> compare (rank c1) (rank c2)
    where
      rank :: Constraint -> Int
      rank = \case
        SubMult{}     -> 0
        SubPrekind{}  -> 1
        MeetPrekind{} -> 2
        JoinPrekind{} -> 3
        JoinMult{}    -> 4

instance Located Constraint where
  getSpan = \case
    SubMult     s _ _ -> s
    SubPrekind  s _ _ -> s
    MeetPrekind s _ _ -> s
    JoinPrekind s _ _ -> s
    JoinMult    s _ _ -> s

  setSpan s = \case
    SubMult     _ m1 m2 -> SubMult     s m1 m2
    SubPrekind  _ v1 v2 -> SubPrekind  s v1 v2
    MeetPrekind _ ψ  vs -> MeetPrekind s ψ  vs
    JoinPrekind _ ψ  vs -> JoinPrekind s ψ  vs
    JoinMult    _ φ  ms -> JoinMult    s φ  ms
