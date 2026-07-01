-- Collecting and solving multiplicity constraints 
-- (i.e., equations in a 01-bounded join-semilattice)
module Validation.LocalInference.Multiplicities
  ( MultConstraints
  , MultEquation(..)
  , multEq
  , kindEq
  , arrowEq
  , kindEqConstraints
  , kindSubConstraints
  , solveMultConstraints
  , solveMultConstraintsDU
  , solveMultConstraintsDUDF
  ) where

import Syntax.Base
import Syntax.Kind (Multiplicity(..), pattern Un)
import Syntax.Kind qualified as K
import Syntax.Provenance (Origin(..), Reason(..))
import Validation.Base (Validation, incCounter)
import Validation.LocalInference.Substitution (Substitution(..), emptySubs, subsMult)

import Control.Monad (guard)
import Data.List (foldl')
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import Compiler.Bug (internalError)

type MultConstraints = [MultEquation]

-- | An equation between two multiplicities.
data MultEquation = MultEquation Multiplicity Origin Multiplicity Origin

-- | Build an equation between two multiplicities.
multEq :: Reason -> Multiplicity -> Multiplicity -> MultEquation
multEq r m1 m2 = MultEquation m1 (Origin (getSpan m1) r) m2 (Origin (getSpan m2) r)

-- | Specialized builders for multiplicity equations-
kindEq, arrowEq :: Multiplicity -> Multiplicity -> MultEquation
kindEq  = multEq FromKind
arrowEq = multEq FromArrow

kindEqConstraints :: K.Kind -> K.Kind -> MultConstraints
kindEqConstraints = \cases
  (K.Proper _ m1 pk1) (K.Proper _ m2 pk2) | pk1 == pk2 -> [kindEq m1 m2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> kindEqConstraints k11 k21
                                          ++ kindEqConstraints k12 k22
  _ _ -> []

kindSubConstraints :: K.Kind -> K.Kind -> MultConstraints
kindSubConstraints = \cases
  (K.Proper _ m1 pk1) (K.Proper _ m2 pk2) | pk1 K.<: pk2 -> [kindEq (K.join m1 m2) m2]
  (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> kindSubConstraints k21 k11
                                          ++ kindSubConstraints k12 k22
  _ _ -> []

-- The substitution accumulated so far and the next negative internal ID.
data SolverState = SolverState !(Map.Map Variable Multiplicity) !Int

-- | Solves the equations, returning he first most general unifier
-- found in breadth-first search. On failure, returns the first
-- equation with no solution (with the accumulated substitution applied).
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
-- Note that the unifier might include free choices, which include fresh variables not 
-- found in the constraints. To default these to `Un`, use `solveMultConstraintsDUDF`.
solveMultConstraints :: MultConstraints -> Validation (Either MultEquation Substitution)
solveMultConstraints eqs = case solve eqs of
  Left eq         -> return (Left eq)
  Right (Θ ivtms) -> do
    let freshes = Set.unions [either (const Set.empty) freshIn it | (_, it) <- ivtms]
    ren <- Map.fromList <$> for (Set.toList freshes) 
      \v -> (v,) . (\i -> v {external = "ṃ" ++ show i, internal = i}) <$> incCounter     
    return (Right (Θ [(φ, fmap (rename ren) it) | (φ, it) <- ivtms]))
  where
    freshIn = \case
      Lin{}      -> Set.empty
      Sup _ lvφs -> Set.fromList [φ | (_, φ) <- lvφs, internal φ < -1]
    rename r = \case
      m@Lin{}    -> m
      Sup sp lvφs -> Sup sp [(lv, Map.findWithDefault φ φ r) | (lv, φ) <- lvφs]
