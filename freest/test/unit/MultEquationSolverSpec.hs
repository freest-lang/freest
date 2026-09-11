module MultEquationSolverSpec (spec) where

import Syntax.Base
import Syntax.Kind (Multiplicity(..))
import Syntax.Provenance (Origin(..))
import Validation.Base (emptyValidationState, runValidation)
import Validation.LocalInference.Multiplicities
import Validation.LocalInference.Substitution (Substitution(..))

import Data.Set qualified as Set
import Test.Hspec

spec :: Spec
spec = describe "Multiplicity equation solver (ACUI)" $ do
  it "satisfies an equation over a variable the kind unifier minted" $
    case solved [eq [x, y] [a, b]] of
      Just θ  -> atomsUnder θ [x, y] `shouldBe` atomsUnder θ [a, b]
      Nothing -> expectationFailure "expected a solution"
  it "admits a variable the kind unifier minted sharing content with only one other side" $
    case solved [eq [x, y] [a, b]] of
      Just θ  -> (atomsUnder θ [x] `Set.intersection` atomsUnder θ [a])
                   `Set.difference` atomsUnder θ [y, b] `shouldNotBe` Set.empty
      Nothing -> expectationFailure "expected a solution"
  it "keeps a variable the kind unifier minted bound under its own id" $
    fmap (\(Θ binds) -> any (same x . fst) binds) (solved [eq [x, y] [a, b]]) `shouldBe` Just True
  where
    o = Origin nullSpan
    x = Variable nullSpan "φ-2" (-2)
    y = Variable nullSpan "φ1001" 1001
    a = Variable nullSpan "φ1002" 1002
    b = Variable nullSpan "φ1003" 1003
    top = Variable nullSpan "1" 999999
    -- 'Variable' equality is by id alone, which is the very confusion under test
    same v w = internal v == internal w && external v == external w
    eq l r = MultEquation (sup l) o (sup r) o
    sup vs = Sup nullSpan [(UnifLv, v) | v <- vs]

    solved eqs = case runValidation emptyValidationState (solveMultConstraints eqs) of
      Right (Right θ) -> Just θ
      _               -> Nothing

    atomsUnder (Θ binds) = Set.unions . map (go [])
      where
        go seen v = case [m | (v', Right m) <- binds, same v' v] of
          Sup _ as : _ | not (any (same v) seen) -> Set.unions [go (v : seen) v' | (_, v') <- as]
          Lin{} : _                              -> Set.singleton (named top)
          _                                      -> Set.singleton (named v)
        named v = (external v, internal v)
