module NormalisationYieldsWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( ValidationState, buildValidationState )
import Validation.Normalisation ( normalise, isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
-- import           Debug.Trace

-- This test should be called with well-formed types only

-- Note: this spec tests very little. As it is, the normalise function returns a
-- whnf, if it returns at all.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T normalises to U, then U is a whnf" 
  errorsAreFailures
  \(t, _, m) -> normYieldsWhnf (buildValidationState m) t `shouldBe` True

normYieldsWhnf :: ValidationState -> T.Type -> Bool
normYieldsWhnf vs t = isWhnf {-$ trace (show $ normalise vs t)-} (normalise vs t)
