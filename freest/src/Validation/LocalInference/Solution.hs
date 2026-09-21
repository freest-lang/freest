-- The unified kind-inference solution and its application to the kinded AST
-- (the analogue of GHC zonking): one map per sort of solvable variable
-- (whole-kind, baseKind, multiplicity), applied uniformly to every kind
-- annotation. Only solvable (UnifLv/InstLv) variables are touched; object-level
-- variables are left alone.
module Validation.LocalInference.Solution
  ( KindSolution(..)
  , KindSubst
  , chaseShapeTypeWith
  , resolveKind
  , resolveMult
  , resolveType
  , resolveModule
  , resolveShapeTypeOpen
  , resolveShapeOpen
  , resolveShape
  ) where

import Syntax.Base
import Syntax.Kind (Kind(..), Multiplicity(..), BaseKind(..))
import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Internal qualified as TI
import Syntax.Expression qualified as E
import Syntax.Module qualified as M
import Syntax.Declarations qualified as D
import Compiler.Bug ( internalError )

import Data.Bifunctor (bimap, first, second)
import Data.Either (partitionEithers)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | The whole-kind substitution alone: what shape unification has settled so
-- far. This is what a pure algorithm is threaded, the kind-level analogue of
-- the type declarations it already carries.
type KindSubst = Map.Map Variable Kind

-- | A solution from kind inference: a binding for each sort of solvable
-- variable, gathered from the three solvers.
data KindSolution = KindSolution
  { kindVars :: Map.Map Variable Kind          -- ^ whole-kind variables (@K.Var@)
  , baseKinds :: Map.Map Variable BaseKind        -- ^ baseKind variables (@VarBK@)
  , mults    :: Map.Map Variable Multiplicity   -- ^ multiplicity variables
  }

-- | Apply the solution to a kind, resolving whole-kind variables to a fixpoint
-- (a binding may mention further variables), with a visited-set guard against
-- ill-formed cycles.
resolveKind :: KindSolution -> Kind -> Kind
resolveKind sol = go Set.empty
  where
    go seen = \case
      Proper s m bk -> Proper s (resolveMult sol m) (resolveBaseKind sol bk)
      Arrow s k1 k2 -> Arrow s (go seen k1) (go seen k2)
      k@(Var s lv ψ)
        | not (solvable lv)                      -> k
        | ψ `Set.member` seen                    -> k                    -- cycle guard
        | Just k' <- Map.lookup ψ (kindVars sol) -> go (Set.insert ψ seen) k'
        | otherwise                              -> Proper s (Lin s) Top -- unconstrained → top (1T)

-- | Resolve a baseKind, defaulting an unconstrained solvable variable to the
-- top and evaluating the symbolic 'MeetBK' and 'JoinBK' a variable operand left
-- behind. This is their only evaluator, so nothing it returns may still carry
-- one: 'Validation.TypeEquivalence' keys its nonterminals on whole kinds, and a
-- symbolic form and the baseKind it evaluates to would be different keys.
resolveBaseKind :: KindSolution -> BaseKind -> BaseKind
resolveBaseKind sol = grounded . go
  where
    go = \case
      VarBK lv ψ | solvable lv -> Map.findWithDefault Top ψ (baseKinds sol)
      MeetBK bk1 bk2           -> K.meet (go bk1) (go bk2)
      JoinBK bk1 bk2           -> K.join (go bk1) (go bk2)
      bk                       -> bk
    grounded bk = case bk of
      MeetBK{} -> internalError ("symbolic baseKind survived the zonk: " ++ show bk)
      JoinBK{} -> internalError ("symbolic baseKind survived the zonk: " ++ show bk)
      _        -> bk

-- | Apply the solution to a multiplicity: replace each solved solvable atom by
-- its value and join with the remaining (rigid or unsolved) atoms.
resolveMult :: KindSolution -> Multiplicity -> Multiplicity
resolveMult sol = go Set.empty
  where
   go _ m@Lin{} = m
   go seen (Sup s atoms) =
    let (subst, keep) = partitionEithers (map resolve atoms)
        resolve (lv, φ)
          | not (solvable lv)     = Right (lv, φ)                    -- rigid: keep
          | φ `Set.member` seen   = Left (Lin s)                     -- cycle → top
          | Just m <- Map.lookup φ (mults sol) = Left (go (Set.insert φ seen) m)  -- solved: recurse
          | otherwise             = Left (Lin s)                     -- unconstrained → top
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

-- | Settle a kind's shape, leaving both components -- multiplicity and baseKind
-- -- to the component solvers. Shape is ordinary first-order unification, done
-- by 'Validation.LocalInference.Kinds.unifyKindSubs', and it is all typing
-- needs to dispatch on: the smart constructors that bind @Proper _ m bk@
-- irrefutably want to know the kind /is/ proper, not what its components are.
--
-- An unconstrained whole-kind variable becomes proper over components named
-- after it, the same device 'Kinding.resolveQuantBinder' uses: nothing binds
-- it, so the solvers default it exactly as they would the variable.
resolveShape :: KindSolution -> Kind -> Kind
resolveShape = resolveShapeWith True

-- | The zonk for a read taken /during/ the walk: it follows the substitution as
-- far as it goes and leaves a variable nothing has settled alone, so a
-- constraint emitted later can still reach it. 'resolveShape' is the final one,
-- which commits.
resolveShapeOpen :: KindSolution -> Kind -> Kind
resolveShapeOpen = resolveShapeWith False

resolveShapeWith :: Bool -> KindSolution -> Kind -> Kind
resolveShapeWith final sol = go Set.empty
  where
    go seen = \case
      k@Proper{}    -> k
      Arrow s k1 k2 -> Arrow s (go seen k1) (go seen k2)
      k@(Var s lv ψ)
        | not (solvable lv)                 -> k
        | ψ `Set.member` seen               -> k
        | Just k' <- Map.lookup ψ (kindVars sol) -> go (Set.insert ψ seen) k'
        | final                             -> Proper s (Sup s [(lv, ψ)]) (VarBK lv ψ)
        | otherwise                         -> k

-- | 'resolveShapeOpen' over every kind annotation in a type, rewritten in
-- place. Unlike 'resolveType' this must not rebuild through the kinded smart
-- constructors: theirs are derived kinds, and the components they meet and join
-- are still variables at this point.
resolveShapeTypeOpen :: KindSolution -> TK.KindedType -> TK.KindedType
resolveShapeTypeOpen sol = go
  where
    k = resolveShapeOpen sol

    go = \case
      TI.Int s x             -> TI.Int s (k x)
      TI.Float s x           -> TI.Float s (k x)
      TI.Char s x            -> TI.Char s (k x)
      TI.Arrow s x m         -> TI.Arrow s (k x) m
      TI.Quant s x p bk m    -> TI.Quant s (k x) p bk m
      TI.ForallM s x m φs t  -> TI.ForallM s (k x) m φs (go t)
      TI.Void s x k'         -> TI.Void s (k x) (k k')
      TI.Skip s x            -> TI.Skip s (k x)
      TI.End s x p           -> TI.End s (k x) p
      TI.Message s x m p     -> TI.Message s (k x) m p
      TI.Choice s x m p is   -> TI.Choice s (k x) m p is
      TI.Semi s x            -> TI.Semi s (k x)
      TI.Dual s x            -> TI.Dual s (k x)
      TI.TName s x i         -> TI.TName s (k x) i
      TI.DName s x i         -> TI.DName s (k x) i
      TI.Var s x lv a        -> TI.Var s (k x) lv a
      TI.Abs s x aks t       -> TI.Abs s (k x) (map (second k) aks) (go t)
      TI.App s x t ts        -> TI.App s (k x) (go t) (map go ts)

-- | Settle a type's kind shapes through a threaded substitution. The identity
-- under 'mempty': 'resolveShapeOpen' returns a 'Proper' as it stands, recurses
-- structurally through an 'Arrow', and leaves a solvable variable the map does
-- not bind alone, while the walk rebuilds every node with its own constructor.
chaseShapeTypeWith :: KindSubst -> TK.KindedType -> TK.KindedType
chaseShapeTypeWith sub = resolveShapeTypeOpen (KindSolution sub mempty mempty)

-- | Apply the whole solution to every kind annotation in a kinded module —
-- type declarations, kind signatures, datatypes, and definitions.
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

-- | Walk the kind annotations on a pattern's type-variable
-- binders ('PackPat' / 'TypeInPat'), recursively. These carry 'UnifLv' kind
-- vars when the binder kind was omitted (see 'Kinding.resolveExpBndKind').
resolvePat :: KindSolution -> E.Pat Kinded -> E.Pat Kinded
resolvePat sol = \case
  E.PackPat s aks p   -> E.PackPat s (map (second (E.mapBndKind (resolveKind sol))) aks) (resolvePat sol p)
  E.TypeInPat s ak p  -> E.TypeInPat s (second (E.mapBndKind (resolveKind sol)) ak) (resolvePat sol p)
  E.DConsPat s i ps   -> E.DConsPat s i (map (resolvePat sol) ps)
  E.InPat s m p1 p2   -> E.InPat s m (resolvePat sol p1) (resolvePat sol p2)
  E.ChoicePat s m i p -> E.ChoicePat s m i (resolvePat sol p)
  E.AsPat s x p       -> E.AsPat s x (resolvePat sol p)
  p                   -> p

resolveLetDecl :: KindSolution -> E.LetDecl Kinded -> E.LetDecl Kinded
resolveLetDecl sol = \case
  E.ValDef p rhs    -> E.ValDef (resolvePat sol p) (resolveRHS sol rhs)
  E.FnDef x clauses -> E.FnDef x (map (bimap (map (mapLevel (resolvePat sol) id id)) (resolveRHS sol)) clauses)
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
  E.Abs s ps m e  -> E.Abs s (map (mapLevel (bimap (resolvePat sol) (fmap (resolveType sol))) (second (E.mapBndKind (resolveKind sol))) id) ps) m (resolveExp sol e)
  E.Pack s ts e   -> E.Pack s (map (resolveType sol) ts) (resolveExp sol e)
  E.Asc s e t     -> E.Asc s (resolveExp sol e) (resolveType sol t)
  E.Let s lds e   -> E.Let s (map (resolveLetDecl sol) lds) (resolveExp sol e)
  E.Case s e brs  -> E.Case s (resolveExp sol e) (map (bimap (resolvePat sol) (resolveRHS sol)) brs)
  E.If s e1 e2 e3 -> E.If s (resolveExp sol e1) (resolveExp sol e2) (resolveExp sol e3)
  E.List s es     -> E.List s (map (resolveExp sol) es)
  E.Channel s t   -> E.Channel s (resolveType sol t)
  E.SendType s t  -> E.SendType s (resolveType sol t)
  E.SectionL s e op   -> E.SectionL s (resolveExp sol e) op
  E.SectionR s x op e -> E.SectionR s x op (resolveExp sol e)
  e               -> e
