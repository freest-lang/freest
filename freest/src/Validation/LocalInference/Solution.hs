-- The unified kind-inference solution and its application to the kinded AST
-- (the analogue of GHC zonking): one map per sort of solvable variable
-- (whole-kind, prekind, multiplicity), applied uniformly to every kind
-- annotation. Only solvable (UnifLv/InstLv) variables are touched; object-level
-- variables are left alone.
module Validation.LocalInference.Solution
  ( KindSolution(..)
  , resolveKind
  , resolveType
  ) where

import Syntax.Base
import Syntax.Kind (Kind(..), Multiplicity(..), Prekind)
import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as TK
import Validation.LocalInference.Prekinds (applyPrekindSubst)

import Data.Bifunctor (second)
import Data.Either (partitionEithers)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | A solution from kind inference: a binding for each sort of solvable
-- variable, gathered from the three solvers.
data KindSolution = KindSolution
  { kindVars :: Map.Map Variable Kind          -- ^ whole-kind variables (@K.Var@)
  , prekinds :: Map.Map Variable Prekind        -- ^ prekind variables (@VarPK@)
  , mults    :: Map.Map Variable Multiplicity   -- ^ multiplicity variables
  }

-- | Apply the solution to a kind, resolving whole-kind variables to a fixpoint
-- (a binding may mention further variables), with a visited-set guard against
-- ill-formed cycles.
resolveKind :: KindSolution -> Kind -> Kind
resolveKind sol = go Set.empty
  where
    go seen = \case
      Proper s m pk -> Proper s (resolveMult sol m) (applyPrekindSubst (prekinds sol) pk)
      Arrow s k1 k2 -> Arrow s (go seen k1) (go seen k2)
      k@(Var _ lv ψ)
        | solvable lv, not (ψ `Set.member` seen), Just k' <- Map.lookup ψ (kindVars sol)
            -> go (Set.insert ψ seen) k'
        | otherwise -> k

-- | Apply the solution to a multiplicity: replace each solved solvable atom by
-- its value and join with the remaining (rigid or unsolved) atoms.
resolveMult :: KindSolution -> Multiplicity -> Multiplicity
resolveMult sol = \case
  m@Lin{}     -> m
  Sup s atoms ->
    let (subst, keep) = partitionEithers (map resolve atoms)
        resolve (lv, φ)
          | solvable lv, Just m <- Map.lookup φ (mults sol) = Left m
          | otherwise                                       = Right (lv, φ)
    in foldr K.join (Sup s keep) subst

-- | Apply the solution to every kind annotation in a type, reconstructing each
-- node through the kinded smart constructors so derived kinds are recomputed
-- from resolved parts. Modelled on 'Validation.Substitution.subsMultType', but
-- without object-level capture handling: the solution only touches solvable
-- variables, while binders are object-level.
resolveType :: KindSolution -> TK.KindedType -> TK.KindedType
resolveType sol = \case
  TK.Arrow s m           -> TK.Arrow s (resolveMult sol m)
  TK.AppForall s m aks t -> TK.AppForall s (resolveMult sol m) (kinds aks) (resolveType sol t)
  TK.AppExists s aks t   -> TK.AppExists s (kinds aks) (resolveType sol t)
  TK.ForallM s m φs t    -> TK.ForallM s (resolveMult sol m) φs (resolveType sol t)
  TK.Void s k            -> TK.Void s (resolveKind sol k)
  TK.Var s k lv a        -> TK.Var s (resolveKind sol k) lv a
  TK.Abs s aks t         -> TK.Abs s (kinds aks) (resolveType sol t)
  TK.App s t ts          -> TK.App s (resolveType sol t) (map (resolveType sol) ts)
  t                      -> t
  where
    kinds = map (second (resolveKind sol))
