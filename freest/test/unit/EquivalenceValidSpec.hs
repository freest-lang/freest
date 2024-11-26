module EquivalenceValidSpec (spec) where

import           TypeEquivalence.TypeEquivalence (equivalent)
import           Test.Hspec
import           UnitSpecUtils (mkSpec)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkSpec
  "test/unit/EquivalenceValid.test" 
  "Valid equivalence tests" 
  \(t,u,m) -> it
    (show t ++ " ~ " ++ show u)
    (equivalent m t u `shouldBe` True)
