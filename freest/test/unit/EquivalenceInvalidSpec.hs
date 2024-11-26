module EquivalenceInvalidSpec (spec) where

import           TypeEquivalence.TypeEquivalence (equivalent)
import           Test.Hspec
import           UnitSpecUtils (mkSpec)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkSpec
  "test/unit/EquivalenceInvalid.test" 
  "Invalid equivalence tests" 
  \(t,u,m) -> it
    (show t ++ " /~ " ++ show u)
    (equivalent m t u `shouldBe` False)
