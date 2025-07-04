module NormalisationIsIdempotentSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( ValidationState, buildValidationState )
import Validation.Normalisation ( normalise )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Validation.Kinding ( runKindModule )

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "normalise t == normalise (normalise t)" 
  errorsAreFailures
  \(t, _, m) -> normalisationIsIdempotent (buildValidationState m) t `shouldBe` True

normalisationIsIdempotent :: ValidationState -> T.Type -> Bool
normalisationIsIdempotent vs t = normalise vs t == normalise vs (normalise vs t)
