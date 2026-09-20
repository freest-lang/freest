-- The unified kind-inference solution and its application to the kinded AST
-- (the analogue of GHC zonking): one map per sort of solvable variable
-- (whole-kind, baseKind, multiplicity), applied uniformly to every kind
-- annotation. Only solvable (UnifLv/InstLv) variables are touched; object-level
-- variables are left alone.
module Validation.LocalInference.Solution
  ( KindSolution(..)
  , resolveKind
  , resolveMult
  , resolveType
  , resolveModule
  , resolveShapeModule
  , resolveShapeType
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

-- | The pair of resolvers a zonk walks a module with. Two exist: the full
-- solution, and the one that settles a kind's shape alone.
data Zonk = Zonk
  { zKind :: Kind -> Kind
  , zType :: TK.KindedType -> TK.KindedType
  }

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

-- | 'resolveShape' for a zonk run /during/ the walk. It refuses a binding whose
-- components the unifier invented ('instLike', negative ids): those are defined
-- by leaf constraints the caller does not keep, so writing them into the AST
-- orphans them -- nothing can bind them and the final zonk defaults them to
-- @1T@. Such a variable is left alone for the final solve to settle.
resolveShapeOpen :: KindSolution -> Kind -> Kind
resolveShapeOpen = resolveShapeWith False

resolveShapeWith :: Bool -> KindSolution -> Kind -> Kind
resolveShapeWith final sol = go Set.empty
  where
    go seen = \case
      k@Proper{}    -> k
      Arrow s k1 k2 -> Arrow s (go seen k1) (go seen k2)
      k@(Var s lv ψ)
        | not (solvable lv)                      -> k
        | ψ `Set.member` seen                    -> k
        | Just k' <- Map.lookup ψ (kindVars sol)
        , final || not (invented k')             -> go (Set.insert ψ seen) k'
        | final                                  -> Proper s (Sup s [(lv, ψ)]) (VarBK lv ψ)
        | otherwise                              -> k

-- | Does this kind mention a variable the unifier invented for itself?
invented :: Kind -> Bool
invented = \case
  Proper _ m bk -> inM m || inB bk
  Arrow _ a b   -> invented a || invented b
  Var _ _ v     -> internal v < 0
  where
    inM = \case Sup _ as -> any ((< 0) . internal . snd) as; _ -> False
    inB = \case
      VarBK _ v  -> internal v < 0
      MeetBK a b -> inB a || inB b
      JoinBK a b -> inB a || inB b
      _          -> False

-- | 'resolveShape' over every kind annotation in a type, rewritten in place.
-- Unlike 'resolveType' this must not rebuild through the kinded smart
-- constructors: theirs are derived kinds, and the components they meet and join
-- are still variables at this point.
resolveShapeType :: KindSolution -> TK.KindedType -> TK.KindedType
resolveShapeType = resolveShapeTypeWith resolveShape

-- | 'resolveShapeType' with 'resolveShapeOpen'.
resolveShapeTypeOpen :: KindSolution -> TK.KindedType -> TK.KindedType
resolveShapeTypeOpen = resolveShapeTypeWith resolveShapeOpen

resolveShapeTypeWith :: (KindSolution -> Kind -> Kind) -> KindSolution -> TK.KindedType -> TK.KindedType
resolveShapeTypeWith res sol = go
  where
    k = res sol
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

-- | Apply the whole solution to a module.
resolveModule :: KindSolution -> M.KindedModule -> M.KindedModule
resolveModule sol = zonkModule (Zonk (resolveKind sol) (resolveType sol))

-- | Apply the shapes alone, which is what typing dispatches on; both components
-- stay symbolic, so neither is decided before the expressions that constrain it
-- have been walked. 'Compiler.Pipeline' applies the rest once typing is done.
resolveShapeModule :: KindSolution -> M.KindedModule -> M.KindedModule
resolveShapeModule sol = zonkModule (Zonk (resolveShape sol) (resolveShapeType sol))

-- | Walk every kind annotation in a kinded module — type declarations, kind
-- signatures, datatypes, and definitions — with the given resolvers.
zonkModule :: Zonk -> M.KindedModule -> M.KindedModule
zonkModule z m = m
  { M.typeDecls   = Map.map (second (zType z)) (M.typeDecls m)
  , M.kindSigs    = Map.map (zKind z) (M.kindSigs m)
  , M.dataDecls   = zonkDataDecls (M.dataDecls m)
  , M.definitions = map (zonkLetDecl z) (M.definitions m)
  }
  where
    zonkDataDecls (D.DataDecls cons types) = D.DataDecls
      (Map.map (second (map (zType z))) cons)
      (Map.map (first (map (second (zKind z)))) types)

-- | Walk the kind annotations on a pattern's type-variable
-- binders ('PackPat' / 'TypeInPat'), recursively. These carry 'UnifLv' kind
-- vars when the binder kind was omitted (see 'Kinding.resolveExpBndKind').
zonkPat :: Zonk -> E.Pat Kinded -> E.Pat Kinded
zonkPat z = \case
  E.PackPat s aks p   -> E.PackPat s (map (second (E.mapBndKind (zKind z))) aks) (zonkPat z p)
  E.TypeInPat s ak p  -> E.TypeInPat s (second (E.mapBndKind (zKind z)) ak) (zonkPat z p)
  E.DConsPat s i ps   -> E.DConsPat s i (map (zonkPat z) ps)
  E.InPat s m p1 p2   -> E.InPat s m (zonkPat z p1) (zonkPat z p2)
  E.ChoicePat s m i p -> E.ChoicePat s m i (zonkPat z p)
  E.AsPat s x p       -> E.AsPat s x (zonkPat z p)
  p                   -> p

zonkLetDecl :: Zonk -> E.LetDecl Kinded -> E.LetDecl Kinded
zonkLetDecl z = \case
  E.ValDef p rhs    -> E.ValDef (zonkPat z p) (zonkRHS z rhs)
  E.FnDef x clauses -> E.FnDef x (map (bimap (map (mapLevel (zonkPat z) id id)) (zonkRHS z)) clauses)
  E.TypeSig xs t    -> E.TypeSig xs (zType z t)
  E.Mutual lds      -> E.Mutual (map (zonkLetDecl z) lds)

zonkRHS :: Zonk -> E.RHS Kinded -> E.RHS Kinded
zonkRHS z = \case
  E.GuardedRHS ges w -> E.GuardedRHS (map (bimap (zonkExp z) (zonkExp z)) ges) (resolveWhere w)
  E.UnguardedRHS e w -> E.UnguardedRHS (zonkExp z e) (resolveWhere w)
  where
    resolveWhere = fmap (map (zonkLetDecl z))

zonkExp :: Zonk -> E.KindedExp -> E.KindedExp
zonkExp z = \case
  E.App s e args  -> E.App s (zonkExp z e) (map (mapLevel (zonkExp z) (zType z) id) args)
  E.Abs s ps m e  -> E.Abs s (map (mapLevel (bimap (zonkPat z) (fmap (zType z))) (second (E.mapBndKind (zKind z))) id) ps) m (zonkExp z e)
  E.Pack s ts e   -> E.Pack s (map (zType z) ts) (zonkExp z e)
  E.Asc s e t     -> E.Asc s (zonkExp z e) (zType z t)
  E.Let s lds e   -> E.Let s (map (zonkLetDecl z) lds) (zonkExp z e)
  E.Case s e brs  -> E.Case s (zonkExp z e) (map (bimap (zonkPat z) (zonkRHS z)) brs)
  E.If s e1 e2 e3 -> E.If s (zonkExp z e1) (zonkExp z e2) (zonkExp z e3)
  E.List s es     -> E.List s (map (zonkExp z) es)
  E.Channel s t   -> E.Channel s (zType z t)
  E.SendType s t  -> E.SendType s (zType z t)
  E.SectionL s e op   -> E.SectionL s (zonkExp z e) op
  E.SectionR s x op e -> E.SectionR s x op (zonkExp z e)
  e               -> e
