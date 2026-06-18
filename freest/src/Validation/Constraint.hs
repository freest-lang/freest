{- |
Module      :  Validation.Constraint
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The syntax of constraints generated during type checking, following the
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

import Syntax.Base ( Variable )
import Syntax.Kind ( Multiplicity, Prekind )

import Data.List qualified as List

-- | A single constraint generated during kind checking.
data Constraint
  = SubMult Multiplicity Multiplicity
    -- ^ @m₁ <: m₂@ — multiplicity subtyping.
  | SubPrekind Prekind Prekind
    -- ^ @v₁ <: v₂@ — prekind subtyping.
  | MeetPrekind Variable [Prekind]
    -- ^ @ψ = ⊓_{ℓ∈L} v_ℓ@ — the prekind variable @ψ@ is the meet of the
    -- given prekinds.
  | JoinPrekind Variable [Prekind]
    -- ^ @ψ = ⊔_{ℓ∈L} v_ℓ@ — the prekind variable @ψ@ is the join of the
    -- given prekinds.
  | JoinMult Variable [Multiplicity]
    -- ^ @φ = ⊔_{ℓ∈L} m_ℓ@ — the multiplicity variable @φ@ is the join of
    -- the given multiplicities.

-- | A constraint set.
type Constraints = [Constraint]

instance Show Constraint where
  show = \case
    SubMult m1 m2    -> show m1 ++ " <: " ++ show m2
    SubPrekind v1 v2 -> show v1 ++ " <: " ++ show v2
    MeetPrekind ψ vs -> show ψ ++ " = ⊓ {" ++ List.intercalate ", " (map show vs) ++ "}"
    JoinPrekind ψ vs -> show ψ ++ " = ⊔ {" ++ List.intercalate ", " (map show vs) ++ "}"
    JoinMult φ ms    -> show φ ++ " = ⊔ {" ++ List.intercalate ", " (map show ms) ++ "}"
