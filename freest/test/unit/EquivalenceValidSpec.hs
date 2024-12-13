module EquivalenceValidSpec (spec) where

import           TypeEquivalence.TypeEquivalence (equivalent)
import           Test.Hspec
import           UnitSpecUtils (mkEquivalenceSpec)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  "test/unit/EquivalenceValid.test" 
  "Valid type equivalence tests" 
  \(t,u,m) -> equivalent m t u `shouldBe` True
