-- Collecting and solving multiplicity constraints 
-- (i.e., equations in a 01-bounded join-semilattice)
module Validation.LocalInference.Multiplicities
  ( MultConstraints
  , MultEquation(..)
  , MultSub(..)
  , MultSubConstraints
  , multEq
  , applyMultSubst
  , solveMultSubs
  , solveMultSubsWitnessed
  , kindEqConstraints
  , rigid
  , solvables
  , solveMultConstraints
  ) where

import Syntax.Base
import Syntax.Kind (Multiplicity(..), pattern Un, pattern VarM)
import Syntax.Kind qualified as K
import Syntax.Provenance (Origin(..), Reason(..))
import Validation.Base (Validation, incCounter)

import Control.Monad (guard)
import Data.Bifunctor (first)
import Data.List (foldl')
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import Compiler.Bug (internalError)

type MultConstraints = [MultEquation]

-- | An equation between two multiplicities.
data MultEquation = MultEquation Multiplicity Origin Multiplicity Origin

-- | Build an equation between two multiplicities.
multEq :: Multiplicity -> Multiplicity -> MultEquation
multEq m1 m2 = MultEquation m1 (Origin InSignature (getSpan m1)) m2 (Origin InSignature (getSpan m2))

kindEqConstraints :: K.Kind -> K.Kind -> MultConstraints
kindEqConstraints = \cases
  (K.Proper _ m1 bk1) (K.Proper _ m2 bk2) | bk1 == bk2 -> [multEq m1 m2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> kindEqConstraints k11 k21
                                          ++ kindEqConstraints k12 k22
  _ _ -> []

-- | Leaves naming a kind inference variable are left to the global solve.
-- | A multiplicity with no variable left to solve.
rigid :: Multiplicity -> Bool
rigid = null . solvables

solvables :: Multiplicity -> [Variable]
solvables = \case Lin{} -> []; Sup _ as -> [φ | (lv, φ) <- as, solvable lv]

data MultSub = MultSub Multiplicity Multiplicity Origin

type MultSubConstraints = [MultSub]

applyMultSubst :: Map.Map Variable Multiplicity -> Multiplicity -> Multiplicity
applyMultSubst σ = go Set.empty
  where
    go _    m@Lin{}       = m
    go seen (Sup s atoms) = foldl' K.join (Un s) (map (expand seen s) atoms)
    expand seen s a@(lv, φ)
      | solvable lv, not (Set.member φ seen), Just m <- Map.lookup φ σ =
          go (Set.insert φ seen) m
      | otherwise = Sup s [a]

-- | The paper's Fig. 14: each variable starts at the top and is met with its
-- rigid upper bounds. It only computes; the caller checks.
solveMultSubs :: MultSubConstraints -> Map.Map Variable Multiplicity
solveMultSubs = fst . solveMultSubsWitnessed

-- | 'solveMultSubs', keeping for each variable the bound that last lowered it:
-- the constraint its value came from, which error messages blame, together with
-- the multiplicity it was bounded against, so the blame can be followed through
-- the variables that carried the value.
solveMultSubsWitnessed :: MultSubConstraints -> (Map.Map Variable Multiplicity, Map.Map Variable (Origin, Multiplicity))
solveMultSubsWitnessed cs = first aliasMutual (fixpoint (Map.empty, Map.empty))
  where
    fixpoint st = let st' = foldl' step st cs in if fst st' == fst st then st else fixpoint st'

    step st@(σ, _) (MultSub l r o)
      | rigid r', not (isTop r') = foldl' (meetWith (o, r) r') st (solvables l)
      | otherwise                = st
      where r' = applyMultSubst σ r

    meetWith (o, r) r' (σ, ws) φ =
      let m = K.meet (Map.findWithDefault (Lin (getSpan r')) φ σ) r'
      in ( Map.insert φ m σ
         , if Map.lookup φ σ == Just m then ws else Map.insert φ (o, r) ws )

    -- a mutual pair is an equality descent never sees; unaliased, the two default apart
    aliasMutual σ = foldl' alias σ
      [ (φ, ψ) | MultSub l r _ <- cs
               , VarM _ lv1 φ <- [applyMultSubst σ l], solvable lv1
               , VarM _ lv2 ψ <- [applyMultSubst σ r], solvable lv2
               , φ /= ψ, any (opposite φ ψ) cs ]
    opposite φ ψ (MultSub l r _) = isAtom ψ l && isAtom φ r
    isAtom φ = \case Sup _ [(lv, φ')] -> solvable lv && φ == φ'; _ -> False
    alias σ (φ, ψ)
      | Map.member φ σ = bindTo ψ φ σ
      | Map.member ψ σ = bindTo φ ψ σ
      | otherwise      = bindTo φ ψ σ
    bindTo v rep' σ
      | Map.member v σ = σ
      | root == v      = σ
      | otherwise      = Map.insert v (VarM (getSpan rep') UnifLv root) σ
      where root = rootOf σ rep'
    rootOf σ φ = case Map.lookup φ σ of
      Just (VarM _ lv ψ) | solvable lv -> rootOf σ ψ
      _                                -> φ

    isTop     = \case Lin{} -> True; _ -> False

-- The substitution accumulated so far, and for each variable the requirement that
-- bound it: what error messages blame, as for the bounds.
data SolverState = SolverState (Map.Map Variable Multiplicity) (Map.Map Variable (Origin, Multiplicity))

-- | Solves the equations, returning he first most general unifier
-- found in breadth-first search. On failure, returns the first
-- equation with no solution (with the accumulated substitution applied).
-- The search is /not/ complete — see the note on `unifySup`.
solveMultConstraints :: MultConstraints
                     -> Validation (Either MultEquation (Map.Map Variable Multiplicity, Map.Map Variable (Origin, Multiplicity)))
solveMultConstraints eqs = fmap finish <$> bfs eqs [SolverState Map.empty Map.empty]
  where
  finish (SolverState sub ws) = (Map.map (apply sub) sub, ws)

  bfs :: MultConstraints -> [SolverState] -> Validation (Either MultEquation SolverState)
  bfs = \cases
    []                (st : _) -> pure (Right st)
    []                []       -> internalError "multiplicity unification: no states"
    (mc@(MultEquation l ol r or') : mcs) sts -> do
      let substituted = [(MultEquation (apply sub l) ol (apply sub r) or', st)
                        | st@(SolverState sub _) <- sts]
      -- the left operand is the requirement: it explains the variables of the right,
      -- kept unsubstituted so the blame can be followed through the variables in it
      next <- concat <$> sequence [solveOne (l', Nothing) (r', Just (ol', l)) st
                                  | (MultEquation l' ol' r' _, st) <- substituted]
      case next of
        [] -> pure (Left case substituted of (eq', _) : _ -> eq'; [] -> mc)
        _  -> bfs mcs next

  solveOne :: (Multiplicity, Maybe (Origin, Multiplicity)) -> (Multiplicity, Maybe (Origin, Multiplicity))
           -> SolverState -> Validation [SolverState]
  solveOne = \cases
    (Lin{}, _)     (Lin{}, _)      st -> pure [st]
    (Lin{}, _)     (m@Sup{}, w)    st -> pure (collapseSide w m st)
    (m@Sup{}, w)   (Lin{}, _)      st -> pure (collapseSide w m st)
    (m1@Sup{}, w1) (m2@Sup{}, w2)  st
      | atoms m1 == atoms m2 -> pure [st]
      | otherwise            -> unifySup (m1, w1) (m2, w2) st

  atoms = \case
    Lin{}      -> Set.empty
    Sup _ lvφs -> Set.fromList lvφs

  collapseSide w m (SolverState sub ws) = do
    (lv, φ) <- Set.toList (atoms m)
    guard (solvable lv)
    return $ SolverState (Map.insert φ (Lin (getSpan m)) sub)
                         (maybe ws (\w' -> Map.insert φ w' ws) w)

  -- Most general unifier(s) of `⊔A = ⊔B` modulo ACUI (associativity,
  -- commutativity, idempotence, unit), with the `ObjLv` atoms as constants.
  -- Let AS, BS be the solvable variables of each side (a common variable is in
  -- both). A fresh overlap variable z(x,y) stands for the content shared by
  -- x∈AS and y∈BS; each variable is bound to the join of its row/column of
  -- overlaps, so ⊔A = ⊔(all z) = ⊔B by construction. A constant occurring on one
  -- side only must be absorbed by some solvable variable on the other side —
  -- each absorption choice is a separate unifier (`assignTo`), and that is the
  -- only source of non-unitarity; the overlap construction itself is
  -- deterministic. The absorbing top `Lin` is not handled here but by the
  -- `Lin = Sup` case (`collapseSide`).
  --
  -- INCOMPLETE, deliberately recorded. Only a constant occurring on *one* side
  -- is ever offered to a variable, so no returned unifier gives a variable a
  -- constant occurring on *both*. The witness is `φ ⊔ m = m` with φ solvable and
  -- m rigid: only1 = {φ}, BS = ∅, so φ gets neither an overlap nor an absorbed
  -- constant and the sole answer is `φ ↦ *`, losing the equally valid and
  -- incomparable `φ ↦ m`. Every omitted unifier only ever *raises* a variable,
  -- so the bias is systematically towards `*`, the least element — which for a
  -- multiplicity read as a bound is the least general choice. Not unsoundness:
  -- every answer returned does satisfy the equations.
  unifySup :: (Multiplicity, Maybe (Origin, Multiplicity)) -> (Multiplicity, Maybe (Origin, Multiplicity))
           -> SolverState -> Validation [SolverState]
  unifySup (m1, w1) (m2, w2) (SolverState sub ws) = do
    let s     = getSpan m1
        as1   = atoms m1
        as2   = atoms m2
        only1 = Set.difference as1 as2
        only2 = Set.difference as2 as1
        asS   = [φ | (lv, φ) <- Set.toList as1, solvable lv]   -- solvable vars of A
        bsS   = [φ | (lv, φ) <- Set.toList as2, solvable lv]   -- solvable vars of B
        oL    = [φ | (ObjLv, φ) <- Set.toList only1]           -- only-A constants
        oR    = [φ | (ObjLv, φ) <- Set.toList only2]           -- only-B constants
        pairs = [(x, y) | x <- asS, y <- bsS]
    zf <- Map.fromList <$> for pairs \p -> (p,) . (\i -> Variable s ("ṃ" ++ show i) i) <$> incCounter
    pure do
      guard (null oL || not (null bsS))   -- an only-A constant needs an absorber on the right
      guard (null oR || not (null asS))   -- an only-B constant needs an absorber on the left
      assignL <- assignTo oL bsS
      assignR <- assignTo oR asS
      let absorbed = Map.unionWith Set.union assignL assignR
          asSet    = Set.fromList asS
          bsSet    = Set.fromList bsS
          bind acc v =
            let row = [(InstLv, zf Map.! (v, y)) | Set.member v asSet, y <- bsS]
                col = [(InstLv, zf Map.! (x, v)) | Set.member v bsSet, x <- asS]
                rig = [(ObjLv, r) | r <- Set.toList (Map.findWithDefault Set.empty v absorbed)]
            in Map.insert v (Sup s (row ++ col ++ rig)) acc
          toBind = Set.toList (Set.union asSet bsSet)
          witness acc v = maybe acc (\w' -> Map.insert v w' acc)
                            (if Set.member v bsSet then w2 else w1)
      return (SolverState (foldl' bind sub toBind) (foldl' witness ws toBind))

  apply :: Map.Map Variable Multiplicity -> Multiplicity -> Multiplicity
  apply sub = go Set.empty
    where
      go _    m@Lin{}      = m
      go seen (Sup s lvφs) = foldl' K.join (Un s) (map (expand seen s) lvφs)
      expand seen s a@(lv, φ)
        | solvable lv, Just m <- Map.lookup φ sub =
            if Set.member φ seen then Un s else go (Set.insert φ seen) m
        | otherwise = Sup s [a]

  assignTo :: [Variable] -> [Variable] -> [Map.Map Variable (Set Variable)]
  assignTo = \cases
    []     _         -> [Map.empty]
    (c:cs) absorbers -> do
      u    <- absorbers
      rest <- assignTo cs absorbers
      return (Map.insertWith Set.union u (Set.singleton c) rest)
