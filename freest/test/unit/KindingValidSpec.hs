module KindingValidSpec (spec) where

import           Validation.Kinding
import           UnitSpecUtils
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Valid kinding tests" 
  \case
    (t, Nothing, m) -> case runKindModule m >>= (`runSynth` t) of 
      Left es -> expectationFailure (unlines $ map show es)
      _       -> return ()
    (t, Just k, m) -> case runKindModule m >>= \m -> runCheck m t k of 
      Left es -> expectationFailure (unlines $ map show es)
      _       -> return ()
