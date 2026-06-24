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
    (InstLv, φ) <- Set.toList (atoms m)
    return $ SolverState (Map.insert φ (Lin (getSpan m)) sub) n

  unifySup :: Multiplicity -> Multiplicity -> SolverState -> [SolverState]
  unifySup m1 m2 (SolverState sub n0) = do
    let s     = getSpan m1
        as1   = atoms m1
        as2   = atoms m2
        only1 = Set.difference as1 as2
        only2 = Set.difference as2 as1
        ovsL  = [φ | (ObjLv,  φ) <- Set.toList only1]
        ovsR  = [φ | (ObjLv,  φ) <- Set.toList only2]
        ivsL  = [φ | (InstLv, φ) <- Set.toList only1]
        ivsR  = [φ | (InstLv, φ) <- Set.toList only2]
        ivs2   = [φ | (InstLv, φ) <- Set.toList as2]
        ivs1   = [φ | (InstLv, φ) <- Set.toList as1]
    guard (null ovsL || not (null ivs2))   -- left-only ObjLv needs absorber on right
    guard (null ovsR || not (null ivs1))   -- right-only ObjLv needs absorber on left
    assignL <- assignTo ovsL ivs2
    assignR <- assignTo ovsR ivs1
    let merged          = Map.unionWith Set.union assignL assignR
        toBind          = Set.toList (Set.fromList (ivsL ++ ivsR ++ Map.keys merged))
        pairs           = [(x, y) | x <- ivsL, y <- ivsR]
        (pairFresh, n1) = allocFresh s n0 pairs
        ivsLSet          = Set.fromList ivsL
        ivsRSet          = Set.fromList ivsR
        bind acc u =
          let absorbed  = Map.findWithDefault Set.empty u merged
              objAtoms  = [(ObjLv, φ) | φ <- Set.toList absorbed]
              freshAtms
                | Set.member u ivsLSet = [(InstLv, pairFresh Map.! (u, y)) | y <- ivsR]
                | Set.member u ivsRSet = [(InstLv, pairFresh Map.! (x, u)) | x <- ivsL]
                | otherwise           = []
          in Map.insert u (Sup s (objAtoms ++ freshAtms)) acc
    return (SolverState (foldl' bind sub toBind) n1)

  apply :: Map.Map Variable Multiplicity -> Multiplicity -> Multiplicity
  apply sub = \case
    m@Lin{}      -> m
    (Sup s lvφs) -> foldl' K.join (Un s) (map expand lvφs)
      where
        expand = \case
          (InstLv, φ) | Just m <- Map.lookup φ sub -> apply sub m
          a                                        -> Sup s [a]

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
