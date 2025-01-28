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
  \(t, _, m) -> case runSynth m t of 
    Left _ -> return ()
    Right _ -> expectationFailure "An error was expected but none was thrown."
