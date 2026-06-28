-- The unified kind-inference solution and its application to the kinded AST
-- (the analogue of GHC zonking): one map per sort of solvable variable
-- (whole-kind, prekind, multiplicity), applied uniformly to every kind
-- annotation. Only solvable (UnifLv/InstLv) variables are touched; object-level
-- variables are left alone.
module Validation.LocalInference.Solution
  ( KindSolution(..)
  , resolveKind
  , resolveType
  , resolveModule
  ) where

import Syntax.Base
import Syntax.Kind (Kind(..), Multiplicity(..), Prekind(..))
import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as TK
import Syntax.Expression qualified as E
import Syntax.Module qualified as M
import Syntax.Declarations qualified as D

import Data.Bifunctor (bimap, first, second)
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
      Proper s m pk -> Proper s (resolveMult sol m) (resolvePrekind sol pk)
      Arrow s k1 k2 -> Arrow s (go seen k1) (go seen k2)
      k@(Var s lv ψ)
        | not (solvable lv)                      -> k
        | ψ `Set.member` seen                    -> k                    -- cycle guard
        | Just k' <- Map.lookup ψ (kindVars sol) -> go (Set.insert ψ seen) k'
        | otherwise                              -> Proper s (Lin s) Top -- unconstrained → top (1T)

-- | Resolve a prekind, defaulting an unconstrained solvable variable to the top.
resolvePrekind :: KindSolution -> Prekind -> Prekind
resolvePrekind sol = \case
  VarPK lv ψ | solvable lv -> Map.findWithDefault Top ψ (prekinds sol)
  pk                       -> pk

-- | Apply the solution to a multiplicity: replace each solved solvable atom by
-- its value and join with the remaining (rigid or unsolved) atoms.
resolveMult :: KindSolution -> Multiplicity -> Multiplicity
resolveMult sol = \case
  m@Lin{}     -> m
  Sup s atoms ->
    let (subst, keep) = partitionEithers (map resolve atoms)
        resolve (lv, φ)
          | not (solvable lv)                  = Right (lv, φ)   -- rigid: keep
          | Just m <- Map.lookup φ (mults sol) = Left m          -- solved
          | otherwise                          = Left (Lin s)    -- unconstrained → top (1)
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
  TK.TName s k i         -> TK.TName s (resolveKind sol k) i
  TK.DName s k i         -> TK.DName s (resolveKind sol k) i
  TK.Abs s aks t         -> TK.Abs s (kinds aks) (resolveType sol t)
  TK.App s t ts          -> TK.App s (resolveType sol t) (map (resolveType sol) ts)
  t                      -> t
  where
    kinds = map (second (resolveKind sol))

-- | Apply the solution to every kind annotation in a kinded module — type
-- declarations, kind signatures, datatypes, and definitions.
resolveModule :: KindSolution -> M.KindedModule -> M.KindedModule
resolveModule sol m = m
  { M.typeDecls   = Map.map (second (resolveType sol)) (M.typeDecls m)
  , M.kindSigs    = Map.map (resolveKind sol) (M.kindSigs m)
  , M.dataDecls   = resolveDataDecls (M.dataDecls m)
  , M.definitions = map (resolveLetDecl sol) (M.definitions m)
  }
  where
    resolveDataDecls (D.DataDecls cons types) = D.DataDecls
      (Map.map (second (map (resolveType sol))) cons)
      (Map.map (first (map (second (resolveKind sol)))) types)

resolveLetDecl :: KindSolution -> E.LetDecl Kinded -> E.LetDecl Kinded
resolveLetDecl sol = \case
  E.ValDef p rhs    -> E.ValDef p (resolveRHS sol rhs)
  E.FnDef x clauses -> E.FnDef x (map (second (resolveRHS sol)) clauses)
  E.TypeSig xs t    -> E.TypeSig xs (resolveType sol t)
  E.Mutual lds      -> E.Mutual (map (resolveLetDecl sol) lds)

resolveRHS :: KindSolution -> E.RHS Kinded -> E.RHS Kinded
resolveRHS sol = \case
  E.GuardedRHS ges w -> E.GuardedRHS (map (bimap (resolveExp sol) (resolveExp sol)) ges) (resolveWhere w)
  E.UnguardedRHS e w -> E.UnguardedRHS (resolveExp sol e) (resolveWhere w)
  where
    resolveWhere = fmap (map (resolveLetDecl sol))

resolveExp :: KindSolution -> E.KindedExp -> E.KindedExp
resolveExp sol = \case
  E.App s e args  -> E.App s (resolveExp sol e) (map (mapLevel (resolveExp sol) (resolveType sol) id) args)
  E.Abs s ps m e  -> E.Abs s (map (mapLevel (second (fmap (resolveType sol))) (second (resolveKind sol)) id) ps) m (resolveExp sol e)
  E.Pack s ts e   -> E.Pack s (map (resolveType sol) ts) (resolveExp sol e)
  E.Asc s e t     -> E.Asc s (resolveExp sol e) (resolveType sol t)
  E.Let s lds e   -> E.Let s (map (resolveLetDecl sol) lds) (resolveExp sol e)
  E.Semi s e1 e2  -> E.Semi s (resolveExp sol e1) (resolveExp sol e2)
  E.Case s e brs  -> E.Case s (resolveExp sol e) (map (second (resolveRHS sol)) brs)
  E.If s e1 e2 e3 -> E.If s (resolveExp sol e1) (resolveExp sol e2) (resolveExp sol e3)
  E.Channel s t   -> E.Channel s (resolveType sol t)
  E.SendType s t  -> E.SendType s (resolveType sol t)
  e               -> e
