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
  ["test/unit/KindingValid.test"]
  "Valid kinding tests" 
  \(t, mk, m) ->
    mk & \case Just  k -> maybeLeft (runCheck m t k)
               Nothing -> maybeLeft (runSynth m t)
       & \case Just es -> expectationFailure (unlines $ map show es)
               Nothing -> return ()
