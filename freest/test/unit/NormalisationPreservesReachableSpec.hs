module NormalisationPreservesReachableSpec (spec) where

import Syntax.Base ( getSpan )
import Syntax.Kind
import Syntax.Module qualified as M
import Validation.Base ( ValidationState, buildValidationState )
import Validation.Rename
import Validation.Normalisation
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

main :: IO ()
main = hspec spec

-- This test should be called with well-formed types only

-- If T normalises to U, then reach(T) = reach(U).

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test" ]
  "Normalisation preserves free reachable variables"
  errorsAreFailures
  \cases
    _ (t, Just k, m) ->
      trace ("\n" ++ show t ++ show tReachable ++ " and " ++ show u  ++ show uReachable)
      tReachable == uReachable `shouldBe` True
      where
        vs = buildValidationState m
        tReachable = reachable vs t
        u = normalise vs t
        uReachable = reachable vs u
    _ _ -> expectationFailure "Ill formed test case: kind annotation absent"
