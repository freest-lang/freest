module KindingValidSpec (spec) where

import           Validation.Kinding
import           Test.Hspec
import           UnitSpecUtils
import           Utils
import           Data.Either (isRight)
import           Data.Function ((&))
import qualified Data.Map as Map
import Parser.Scoping (runScoping)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Valid kinding tests" 
  \(t, k, m) -> case runCheck m t k of 
    Left es -> expectationFailure (unlines $ map show es)
    _       -> return ()
