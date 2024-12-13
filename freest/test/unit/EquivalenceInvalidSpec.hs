module EquivalenceInvalidSpec (spec) where

import           TypeEquivalence.TypeEquivalence (equivalent)
import           Test.Hspec
import           UnitSpecUtils (mkEquivalenceSpec)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  "test/unit/EquivalenceInvalid.test" 
  "Invalid equivalence tests" 
  \(t,u,m) -> equivalent m t u `shouldBe` False
