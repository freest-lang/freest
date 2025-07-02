module ReductionPreservesReflectsAbsorbingSpec (spec) where

import Syntax.Base ( getSpan )
import Syntax.Kind
import Syntax.Module qualified as M
import Validation.Base ( buildValidationState, typeDecls )
import Validation.Rename
import Validation.Normalisation
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

main :: IO ()
main = hspec spec

-- This test should be called with well-formed types only

-- If T --> U, then T absorbing iff U absorbing.

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test" ]
  "Reduction preserves and reflects absorbing"
  errorsAreFailures
  \case
    (t, Just k, m) ->
      isWhnf t || 
      trace ("\n" ++ show t ++ showAbs tAbsorbing ++ " and " ++ show u  ++ showAbs uAbsorbing)
        tAbsorbing == uAbsorbing `shouldBe` True
      where
        vs = buildValidationState m
        tAbsorbing = absorbing vs t
        u = reduce (typeDecls vs) t
        uAbsorbing = absorbing vs u
    _ -> expectationFailure "Ill formed test case: kind annotation absent"

showAbs :: Bool -> String
showAbs True = " is absorbing"
showAbs False = " is non absorbing"
