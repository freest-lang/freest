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
  , unsatisfiedMultSub
  , kindEqConstraints
  , kindSubConstraints
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

kindSubConstraints :: K.Kind -> K.Kind -> MultConstraints
kindSubConstraints = \cases
  (K.Proper _ m1 bk1) (K.Proper _ m2 bk2) | bk1 K.<: bk2 -> [multEq (K.join m1 m2) m2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> kindSubConstraints k21 k11
                                          ++ kindSubConstraints k12 k22
  _ _ -> []

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
-- rigid upper bounds. It only computes; 'unsatisfiedMultSub' checks.
solveMultSubs :: Set Variable -> MultSubConstraints -> Map.Map Variable Multiplicity
solveMultSubs undefs cs = raiseLowerBounds (aliasMutual (fixpoint Map.empty))
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
      | Map.member φ σ        = bindTo ψ φ σ
      | Map.member ψ σ        = bindTo φ ψ σ
      | φ `Set.member` undefs = bindTo ψ φ σ
      | otherwise             = bindTo φ ψ σ
    bindTo v rep' σ
      | Map.member v σ = σ
      | root == v      = σ
      | otherwise      = Map.insert v (VarM (getSpan rep') UnifLv root) σ
      where root = rootOf σ rep'
    rootOf σ φ = case Map.lookup φ σ of
      Just (VarM _ lv ψ) | solvable lv -> rootOf σ ψ
      _                                -> φ

    -- the top satisfies a lower bound; only a *-defaulting variable can break one
    raiseLowerBounds σ = foldl' raise σ
      [ (φ, l') | MultSub l r _ <- cs
                , VarM _ lv φ <- [applyMultSubst σ r]
                , solvable lv, φ `Set.member` undefs, not (Map.member φ σ)
                , let l' = applyMultSubst σ l, rigid l' ]
    raise σ (φ, m) =
      Map.insert φ (K.join (Map.findWithDefault (Un (getSpan m)) φ σ) m) σ

    rigid     = null . solvables
    solvables = \case Lin{} -> []; Sup _ as -> [φ | (lv, φ) <- as, solvable lv]
    isTop     = \case Lin{} -> True; _ -> False

unsatisfiedMultSub :: (Multiplicity -> Multiplicity) -> MultSubConstraints -> Maybe MultSub
unsatisfiedMultSub resolve =
  List.find \(MultSub l r _) -> not (resolve l K.<: resolve r)

-- The substitution accumulated so far and the next negative internal ID.
data SolverState = SolverState !(Map.Map Variable Multiplicity) !Int

-- | Solves the equations, returning he first most general unifier
-- found in breadth-first search. On failure, returns the first
-- equation with no solution (with the accumulated substitution applied).
-- The search is /not/ complete — see the note on `unifySup`.
-- Any fresh variables introduced by the solver have a distinct negative
-- internal ID, assuming there are no such IDs in the constraints. 
-- This is done to avoid doing the solving inside `Validation`. 
-- `solveMultConstraints`.
solve :: MultConstraints -> Either MultEquation Substitution
solve eqs = do
  SolverState sub _ <- bfs eqs [SolverState Map.empty (-2)]
  let resolved = Map.map (apply sub) sub
  return $ Map.foldrWithKey (\φ m -> (subsMult φ m <>)) emptySubs resolved
  where
  bfs :: MultConstraints -> [SolverState] -> Either MultEquation SolverState
  bfs = \cases
    []                (st : _) -> Right st
    []                []       -> internalError "multiplicity unification: no states"
    (mc@(MultEquation l ol r or') : mcs) sts -> case next of
      [] -> Left case substituted of (eq', _) : _ -> eq'; [] -> mc
      _  -> bfs mcs next
      where
        substituted = [(MultEquation (apply sub l) ol (apply sub r) or', st)
                      | st@(SolverState sub _) <- sts]
        next        = [st' | (MultEquation l' _ r' _, st) <- substituted
                           , st'          <- solveOne l' r' st]

  solveOne :: Multiplicity -> Multiplicity -> SolverState -> [SolverState]
  solveOne = \cases
    Lin{}    Lin{}    st -> [st]
    Lin{}    m@Sup{}  st -> collapseSide m st
    m@Sup{}  Lin{}    st -> collapseSide m st
    m1@Sup{} m2@Sup{} st
      | atoms m1 == atoms m2 -> [st]
      | otherwise                -> unifySup m1 m2 st

  atoms = \case
    Lin{}      -> Set.empty
    Sup _ lvφs -> Set.fromList lvφs

  collapseSide m (SolverState sub n) = do
    (lv, φ) <- Set.toList (atoms m)
    guard (solvable lv)
    return $ SolverState (Map.insert φ (Lin (getSpan m)) sub) n

  -- Most general unifier(s) of `⊔A = ⊔B` modulo ACUI (associativity,
  -- commutativity, idempotence, unit), with the `ObjLv` atoms as constants.
  -- Let AS, BS be the solvable variables of each side (a common variable is in
  -- both). A fresh region variable z(x,y) stands for the content shared by
  -- x∈AS and y∈BS; each variable is bound to the join of its row/column of
  -- regions, so ⊔A = ⊔(all z) = ⊔B by construction. A constant occurring on one
  -- side only must be absorbed by some solvable variable on the other side —
  -- each absorption choice is a separate unifier (`assignTo`), and that is the
  -- only source of non-unitarity; the region construction itself is
  -- deterministic. The absorbing top `Lin` is not handled here but by the
  -- `Lin = Sup` case (`collapseSide`).
  --
  -- INCOMPLETE, deliberately recorded. Only a constant occurring on *one* side
  -- is ever offered to a variable, so no returned unifier gives a variable a
  -- constant occurring on *both*. The witness is `φ ⊔ m = m` with φ solvable and
  -- m rigid: only1 = {φ}, BS = ∅, so φ gets neither a region nor an absorbed
  -- constant and the sole answer is `φ ↦ *`, losing the equally valid and
  -- incomparable `φ ↦ m`. Every omitted unifier only ever *raises* a variable,
  -- so the bias is systematically towards `*`, the least element — which for a
  -- multiplicity read as a bound is the least general choice. Not unsoundness:
  -- every answer returned does satisfy the equations.
  --
  -- Kind inference no longer sends bounds here (see 'solveMultSubs'); local
  -- inference's 'kindSubConstraints' still does, and still lands on `*`.
  unifySup :: Multiplicity -> Multiplicity -> SolverState -> [SolverState]
  unifySup m1 m2 (SolverState sub n0) = do
    let s     = getSpan m1
        as1   = atoms m1
        as2   = atoms m2
        only1 = Set.difference as1 as2
        only2 = Set.difference as2 as1
        asS   = [φ | (lv, φ) <- Set.toList as1, solvable lv]   -- solvable vars of A
        bsS   = [φ | (lv, φ) <- Set.toList as2, solvable lv]   -- solvable vars of B
        oL    = [φ | (ObjLv, φ) <- Set.toList only1]           -- only-A constants
        oR    = [φ | (ObjLv, φ) <- Set.toList only2]           -- only-B constants
    guard (null oL || not (null bsS))   -- an only-A constant needs an absorber on the right
    guard (null oR || not (null asS))   -- an only-B constant needs an absorber on the left
    assignL <- assignTo oL bsS
    assignR <- assignTo oR asS
    let absorbed = Map.unionWith Set.union assignL assignR
        pairs    = [(x, y) | x <- asS, y <- bsS]
        (zf, n1) = allocFresh s n0 pairs
        asSet    = Set.fromList asS
        bsSet    = Set.fromList bsS
        bind acc v =
          let row = [(InstLv, zf Map.! (v, y)) | Set.member v asSet, y <- bsS]
              col = [(InstLv, zf Map.! (x, v)) | Set.member v bsSet, x <- asS]
              rig = [(ObjLv, r) | r <- Set.toList (Map.findWithDefault Set.empty v absorbed)]
          in Map.insert v (Sup s (row ++ col ++ rig)) acc
        toBind = Set.toList (Set.union asSet bsSet)
    return (SolverState (foldl' bind sub toBind) n1)

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

  allocFresh :: Span -> Int -> [(Variable, Variable)]
             -> (Map.Map (Variable, Variable) Variable, Int)
  allocFresh s = go Map.empty
    where
      go acc n = \case 
        []     -> (acc, n)
        (p:ps) -> go (Map.insert p iv acc) (n - 1) ps
          where iv = Variable s ("ṃ" ++ show (- n)) n

-- | Like `solveMultConstraints`, but defaults any free choice in the original
-- constraints to `Un`.
solveMultConstraintsDU :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraintsDU eqs = fmap (defaultUnbound eqs) <$> solveMultConstraints eqs

-- | Like `solveMultConstraintsDU`, but additionally defaults any free choice introduced
-- by the solver to `Un`.
solveMultConstraintsDUDF :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraintsDUDF eqs =
  pure (defaultFresh . defaultUnbound eqs <$> solve eqs)

-- | Defaults any free choice introduced by the solver to `Un`.
defaultFresh :: Substitution -> Substitution
defaultFresh (Θ ivtms) = Θ [(φ, fmap strip it) | (φ, it) <- ivtms]
  where
    strip = \case
      m@Lin{}     -> m
      Sup sp lvφs -> Sup sp [lvφ | lvφ@(_, φ) <- lvφs, internal φ >= -1]

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

-- | Solves the equations, returning he first most general unifier
-- found in breadth-first search. On failure, returns the first
-- equation with no solution (with the accumulated substitution applied).
-- The search is /not/ complete — see the note on `unifySup`.
-- Note that the unifier might include free choices, which include fresh variables not 
-- found in the constraints. To default these to `Un`, use `solveMultConstraintsDUDF`.
solveMultConstraints :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraints eqs = case solve eqs of
  Left eq         -> return (Left eq)
  Right (Θ ivtms) -> do
    let freshes = Set.unions [Set.fromList [φ | isFresh φ] `Set.union`
                                either (const Set.empty) freshIn it | (φ, it) <- ivtms]
    ren <- Map.fromList <$> for (Set.toList freshes) 
      \v -> (v,) . (\i -> v {external = "ṃ" ++ show i, internal = i}) <$> incCounter     
    return (Right (Θ [(Map.findWithDefault φ φ ren, fmap (rename ren) it) | (φ, it) <- ivtms]))
  where
    -- the kind unifier mints from the same negative range, and 'Variable' equality is by id
    isFresh φ = internal φ < -1
    freshIn = \case
      Lin{}      -> Set.empty
      Sup _ lvφs -> Set.fromList [φ | (_, φ) <- lvφs, isFresh φ]
    rename r = \case
      m@Lin{}    -> m
      Sup sp lvφs -> Sup sp [(lv, Map.findWithDefault φ φ r) | (lv, φ) <- lvφs]
