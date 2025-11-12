module ReachableAreFreeVarsSpec (spec) where

import Syntax.Module qualified as M
import Validation.Base ( ValidationState, buildValidationState )
import Validation.Substitution ( freeVars )
import Validation.Rename ( reachable )

import Data.Set qualified as Set
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

-- reach(T) ⊆ fv(T)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "Free reachable variables are free" 
  errorsAreFailures
  \_ (t, _, m) -> freeVars t `Set.isSubsetOf` reachable (buildValidationState m) t `shouldBe` True
