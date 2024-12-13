module KindingValidSpec (spec) where

import           Validation.Kinding (runSynth, runKindModule)
import           Test.Hspec
import           UnitSpecUtils
import           Data.Either (isRight)
import qualified Data.Map as Map
import Parser.Scoping (runScoping)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Valid kinding tests" 
  \(t,m) -> case runSynth m t of
    Left es -> expectationFailure (unlines $ map show es)
    Right _ -> return ()
