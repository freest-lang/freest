-- Collecting and solving prekind constraints over the chain C <: S <: T.
--
-- Unlike multiplicities (a join-semilattice with surface sums, solved by ACUI),
-- prekinds form a three-element total order with no surface sums; solving is a
-- small fixpoint that seeds every solvable variable to the top (T) and lowers
-- it by greatest-lower-bound (meet), yielding the most general prekind.
module Validation.LocalInference.Prekinds
  ( PrekindConstraint(..)
  , PrekindConstraints
  , PrekindSubst
  , applyPrekindSubst
  , solvePrekindConstraints
  , kindSubPrekindConstraints
  , kindEqPrekindConstraints
  ) where

import Syntax.Base
import Syntax.Kind (Prekind(..), Meet(..), Join(..), Subsort(..))
import Syntax.Kind qualified as K
import Syntax.Provenance (Origin)

import Control.Monad (foldM)
import Data.List (foldl')
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | A constraint over prekinds in the chain @C <: S <: T@. The 'Origin' records
-- where the constraint arose, for error reporting. The variables on the left of
-- a meet/join constraint are inference-generated and solvable by construction.
data PrekindConstraint
  = SubPrekind  Origin Prekind Prekind             -- ^ @υ1 <: υ2@
  | MeetPrekind Origin Variable [Prekind]          -- ^ @ψ = ⨅ υs@
  | JoinPrekind Origin Variable [Prekind]          -- ^ @ψ = ⨆ υs@

type PrekindConstraints = [PrekindConstraint]

-- | A solution mapping prekind variables to prekinds.
type PrekindSubst = Map.Map Variable Prekind

-- | Resolve a prekind through a solution. A solved substitution maps each
-- variable to a ground prekind, so a single lookup suffices.
applyPrekindSubst :: PrekindSubst -> Prekind -> Prekind
applyPrekindSubst sub = \case
  VarPK lv ψ | solvable lv -> Map.findWithDefault (VarPK lv ψ) ψ sub
  pk                       -> pk

-- | Solve a set of prekind constraints, returning the most general unifier or
-- the first constraint with no solution. Every solvable prekind variable is
-- seeded to the top (T) and lowered by meet until a fixpoint is reached; ground
-- and object-level (rigid) prekinds are only checked.
solvePrekindConstraints :: PrekindConstraints -> Either PrekindConstraint PrekindSubst
solvePrekindConstraints cs = go (Map.fromSet (const Top) (solvableVars cs))
  where
    go sub = do
      sub' <- foldM step sub cs
      if sub' == sub then Right sub' else go sub'

    step sub c = case c of
      SubPrekind _ (VarPK lv ψ) υ2 | solvable lv ->
        Right (lower ψ (eval sub υ2) sub)
      SubPrekind _ υ1 υ2
        | eval sub υ1 <: eval sub υ2 -> Right sub
        | otherwise                  -> Left c
      MeetPrekind _ ψ υs -> Right (lower ψ (foldr (meet . eval sub) Top     υs) sub)
      JoinPrekind _ ψ υs -> Right (lower ψ (foldr (join . eval sub) Channel υs) sub)

    -- Lower ψ to the greatest lower bound of its current value and @v@.
    lower ψ v sub = Map.insert ψ (meet (Map.findWithDefault Top ψ sub) v) sub

    eval sub = \case
      VarPK lv ψ | solvable lv -> Map.findWithDefault Top ψ sub
      pk                       -> pk

-- | The solvable prekind variables occurring in a constraint set.
solvableVars :: PrekindConstraints -> Set.Set Variable
solvableVars = Set.unions . map \case
  SubPrekind _ a b   -> pkVars a <> pkVars b
  MeetPrekind _ ψ υs -> Set.insert ψ (foldMap pkVars υs)
  JoinPrekind _ ψ υs -> Set.insert ψ (foldMap pkVars υs)
  where
    pkVars (VarPK lv ψ) | solvable lv = Set.singleton ψ
    pkVars _                          = Set.empty

-- | Decompose a kind subkinding constraint @K1 <: K2@ into its prekind
-- constraints, with arrow domains contravariant. The 'Origin' is threaded from
-- the originating kind constraint (prekinds carry no span of their own).
kindSubPrekindConstraints :: Origin -> K.Kind -> K.Kind -> PrekindConstraints
kindSubPrekindConstraints o = \cases
  (K.Proper _ _ pk1) (K.Proper _ _ pk2) -> [SubPrekind o pk1 pk2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) ->
    kindSubPrekindConstraints o k21 k11 ++ kindSubPrekindConstraints o k12 k22
  _ _ -> []

-- | Decompose a kind equality constraint @K1 = K2@ into prekind constraints
-- (subkinding in both directions).
kindEqPrekindConstraints :: Origin -> K.Kind -> K.Kind -> PrekindConstraints
kindEqPrekindConstraints o k1 k2 =
  kindSubPrekindConstraints o k1 k2 ++ kindSubPrekindConstraints o k2 k1
