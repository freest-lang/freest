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
  , kindEqConstraints
  , kindSubConstraints
  , inferredMult
  , solveMultConstraints
  , solveMultConstraintsDU
  , solveMultConstraintsDUDF
  ) where

import Syntax.Base
import Syntax.Kind (Multiplicity(..), pattern Un, pattern VarM)
import Syntax.Kind qualified as K
import Syntax.Provenance (Origin(..))
import Validation.Base (Validation, incCounter)
import Validation.LocalInference.Substitution (Substitution(..), emptySubs, subsMult)

import Control.Monad (guard)
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
multEq m1 m2 = MultEquation m1 (Origin (getSpan m1)) m2 (Origin (getSpan m2))

kindEqConstraints :: K.Kind -> K.Kind -> MultConstraints
kindEqConstraints = \cases
  (K.Proper _ m1 bk1) (K.Proper _ m2 bk2) | bk1 == bk2 -> [multEq m1 m2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> kindEqConstraints k11 k21
                                          ++ kindEqConstraints k12 k22
  _ _ -> []

-- | Leaves naming a kind inference variable are left to the global solve.
kindSubConstraints :: K.Kind -> K.Kind -> MultConstraints
kindSubConstraints = \cases
  (K.Proper _ m1 bk1) (K.Proper _ m2 bk2)
    | bk1 K.<: bk2, not (inferredMult m1 || inferredMult m2) -> [multEq (K.join m1 m2) m2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> kindSubConstraints k21 k11
                                          ++ kindSubConstraints k12 k22
  _ _ -> []

inferredMult :: Multiplicity -> Bool
inferredMult = \case
  Sup _ as -> any ((== UnifLv) . fst) as
  Lin{}    -> False

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
solveMultSubs cs = aliasMutual (fixpoint Map.empty)
  where
    fixpoint σ = let σ' = foldl' step σ cs in if σ' == σ then σ else fixpoint σ'

    step σ (MultSub l r _)
      | rigid r', not (isTop r') = foldl' (meetWith r') σ (solvables l)
      | otherwise                = σ
      where r' = applyMultSubst σ r

    meetWith r' σ φ =
      Map.insert φ (K.meet (Map.findWithDefault (Lin (getSpan r')) φ σ) r') σ

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

    rigid     = null . solvables
    solvables = \case Lin{} -> []; Sup _ as -> [φ | (lv, φ) <- as, solvable lv]
    isTop     = \case Lin{} -> True; _ -> False

-- The substitution accumulated so far.
newtype SolverState = SolverState (Map.Map Variable Multiplicity)

-- | Solves the equations, returning he first most general unifier
-- found in breadth-first search. On failure, returns the first
-- equation with no solution (with the accumulated substitution applied).
-- The search is /not/ complete — see the note on `unifySup`.
-- Note that the unifier might include free choices, which include fresh variables not 
-- found in the constraints. To default these to `Un`, use `solveMultConstraintsDUDF`.
solveMultConstraints :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraints eqs = fmap finish <$> bfs eqs [SolverState Map.empty]
  where
  finish (SolverState sub) =
    Map.foldrWithKey (\φ m -> (subsMult φ m <>)) emptySubs (Map.map (apply sub) sub)

  bfs :: MultConstraints -> [SolverState] -> Validation (Either MultEquation SolverState)
  bfs = \cases
    []                (st : _) -> pure (Right st)
    []                []       -> internalError "multiplicity unification: no states"
    (mc@(MultEquation l ol r or') : mcs) sts -> do
      let substituted = [(MultEquation (apply sub l) ol (apply sub r) or', st)
                        | st@(SolverState sub) <- sts]
      next <- concat <$> sequence [solveOne l' r' st | (MultEquation l' _ r' _, st) <- substituted]
      case next of
        [] -> pure (Left case substituted of (eq', _) : _ -> eq'; [] -> mc)
        _  -> bfs mcs next

  solveOne :: Multiplicity -> Multiplicity -> SolverState -> Validation [SolverState]
  solveOne = \cases
    Lin{}    Lin{}    st -> pure [st]
    Lin{}    m@Sup{}  st -> pure (collapseSide m st)
    m@Sup{}  Lin{}    st -> pure (collapseSide m st)
    m1@Sup{} m2@Sup{} st
      | atoms m1 == atoms m2 -> pure [st]
      | otherwise            -> unifySup m1 m2 st

  atoms = \case
    Lin{}      -> Set.empty
    Sup _ lvφs -> Set.fromList lvφs

  collapseSide m (SolverState sub) = do
    (lv, φ) <- Set.toList (atoms m)
    guard (solvable lv)
    return $ SolverState (Map.insert φ (Lin (getSpan m)) sub)

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
  --
  -- Kind inference no longer sends bounds here (see 'solveMultSubs'); local
  -- inference's 'kindSubConstraints' still does, and still lands on `*`.
  unifySup :: Multiplicity -> Multiplicity -> SolverState -> Validation [SolverState]
  unifySup m1 m2 (SolverState sub) = do
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
      return (SolverState (foldl' bind sub toBind))

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

-- | Like `solveMultConstraints`, but defaults any free choice in the original
-- constraints to `Un`.
solveMultConstraintsDU :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraintsDU eqs = fmap (defaultUnbound eqs) <$> solveMultConstraints eqs

-- | Like `solveMultConstraintsDU`, but additionally defaults any free choice introduced
-- by the solver to `Un`.
solveMultConstraintsDUDF :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraintsDUDF eqs =
  fmap (defaultFresh eqs . defaultUnbound eqs) <$> solveMultConstraints eqs

-- | Defaults any free choice introduced by the solver to `Un`.
defaultFresh :: MultConstraints -> Substitution -> Substitution
defaultFresh eqs (Θ ivtms) = Θ [(φ, fmap strip it) | (φ, it) <- ivtms]
  where
    input = Set.fromList [φ | MultEquation l _ r _ <- eqs, Sup _ lvφs <- [l, r], (_, φ) <- lvφs]
    strip = \case
      m@Lin{}     -> m
      Sup sp lvφs -> Sup sp [lvφ | lvφ@(_, φ) <- lvφs, φ `Set.member` input]

-- | Substitute `Un` for every instantiation variable that occurs in the
-- constraints but is not bound by the substitution, i.e.,
-- σ ∪ { α ↦ 0 | α ∈ iv(E) ∖ dom(σ) }
defaultUnbound :: MultConstraints -> Substitution -> Substitution
defaultUnbound eqs sub@(Θ ivtms) =
  let bound = Set.fromList [φ | (φ, _) <- ivtms]
      ivE   = Set.fromList
                [ φ | MultEquation l _ r _ <- eqs
                    , Sup _ lvφs <- [l, r]
                    , (InstLv, φ) <- lvφs
                ]
      free  = Set.toList (Set.difference ivE bound)
  in foldr (\φ -> (subsMult φ (Un (getSpan φ)) <>)) sub free
