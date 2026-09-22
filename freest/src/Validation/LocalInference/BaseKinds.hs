-- Collecting and solving baseKind constraints over the chain C <: S <: T.
--
-- Unlike multiplicities (a join-semilattice with surface sums, solved by ACUI),
-- baseKinds form a three-element total order with no surface sums; solving is a
-- small fixpoint that seeds every solvable variable to the top (T) and lowers
-- it by greatest-lower-bound (meet), yielding the most general baseKind.
module Validation.LocalInference.BaseKinds
  ( BaseKindConstraint(..)
  , BaseKindConstraints
  , BaseKindSubst
  , applyBaseKindSubst
  , solveBaseKindConstraints
  , kindSubBaseKindConstraints
  , kindEqBaseKindConstraints
  ) where

import Syntax.Base
import Syntax.Kind (BaseKind(..), Meet(..), Join(..), Subsort(..))
import Syntax.Kind qualified as K
import Syntax.Provenance (Origin)

import Control.Monad (foldM)
import Data.List (foldl')
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | A constraint over baseKinds in the chain @C <: S <: T@. The 'Origin' records
-- where the constraint arose, for error reporting. The variables on the left of
-- a meet/join constraint are inference-generated and solvable by construction.
data BaseKindConstraint
  = SubBaseKind  Origin BaseKind BaseKind             -- ^ @υ1 <: υ2@
  | MeetBaseKind Origin Variable [BaseKind]          -- ^ @ψ = ⨅ υs@
  | JoinBaseKind Origin Variable [BaseKind]          -- ^ @ψ = ⨆ υs@

type BaseKindConstraints = [BaseKindConstraint]

-- | A solution mapping baseKind variables to baseKinds.
type BaseKindSubst = Map.Map Variable BaseKind

-- | Resolve a baseKind through a solution. A solved substitution maps each
-- variable to a ground baseKind, so a single lookup suffices.
applyBaseKindSubst :: BaseKindSubst -> BaseKind -> BaseKind
applyBaseKindSubst sub = \case
  VarBK lv ψ | solvable lv -> Map.findWithDefault (VarBK lv ψ) ψ sub
  bk                       -> bk

-- | Solve a set of baseKind constraints, returning the most general unifier or
-- the first constraint with no solution. Every solvable baseKind variable is
-- seeded to the top (T) and lowered by meet until a fixpoint is reached; ground
-- and object-level (rigid) baseKinds are only checked.
solveBaseKindConstraints :: BaseKindConstraints -> Either BaseKindConstraint BaseKindSubst
solveBaseKindConstraints cs = go (Map.fromSet (const Top) (solvableVars cs))
  where
    go sub = do
      sub' <- foldM step sub cs
      if sub' == sub then Right sub' else go sub'

    step sub c = case c of
      SubBaseKind _ (VarBK lv ψ) υ2 | solvable lv ->
        Right (lower ψ (eval sub υ2) sub)
      SubBaseKind _ υ1 υ2
        | eval sub υ1 <: eval sub υ2 -> Right sub
        | otherwise                  -> Left c
      MeetBaseKind _ ψ υs -> Right (lower ψ (foldr (meet . eval sub) Top     υs) sub)
      JoinBaseKind _ ψ υs -> Right (lower ψ (foldr (join . eval sub) Channel υs) sub)

    -- Lower ψ to the greatest lower bound of its current value and @v@.
    lower ψ v sub = Map.insert ψ (meet (Map.findWithDefault Top ψ sub) v) sub

    eval sub = \case
      VarBK lv ψ | solvable lv -> Map.findWithDefault Top ψ sub
      bk                       -> bk

-- | The solvable baseKind variables occurring in a constraint set.
solvableVars :: BaseKindConstraints -> Set.Set Variable
solvableVars = Set.unions . map \case
  SubBaseKind _ a b   -> pkVars a <> pkVars b
  MeetBaseKind _ ψ υs -> Set.insert ψ (foldMap pkVars υs)
  JoinBaseKind _ ψ υs -> Set.insert ψ (foldMap pkVars υs)
  where
    pkVars (VarBK lv ψ) | solvable lv = Set.singleton ψ
    pkVars _                          = Set.empty

-- | Decompose a kind subkinding constraint @K1 <: K2@ into its baseKind
-- constraints, with arrow domains contravariant. The 'Origin' is threaded from
-- the originating kind constraint (baseKinds carry no span of their own).
kindSubBaseKindConstraints :: Origin -> K.Kind -> K.Kind -> BaseKindConstraints
kindSubBaseKindConstraints o = \cases
  (K.Proper _ _ bk1) (K.Proper _ _ bk2) -> [SubBaseKind o bk1 bk2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) ->
    kindSubBaseKindConstraints o k21 k11 ++ kindSubBaseKindConstraints o k12 k22
  _ _ -> []

-- | Decompose a kind equality constraint @K1 = K2@ into baseKind constraints
-- (subkinding in both directions).
kindEqBaseKindConstraints :: Origin -> K.Kind -> K.Kind -> BaseKindConstraints
kindEqBaseKindConstraints o k1 k2 =
  kindSubBaseKindConstraints o k1 k2 ++ kindSubBaseKindConstraints o k2 k1
