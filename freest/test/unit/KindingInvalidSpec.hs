module KindingInvalidSpec (spec) where

import           Validation.Kinding (runSynth)
import           Test.Hspec
import           UnitSpecUtils (mkKindingSpec)
import           Data.Either (isRight)
import qualified Data.Map as Map

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingInvalid.test" 
  "Invalid kinding tests" 
  \(t,m) -> isRight (runSynth m t) `shouldBe` False
