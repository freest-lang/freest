module KindSynthValidSpec (spec) where

import           Validation.Kinding
import           UnitSpecUtils
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "Valid kind synthesis tests" 
  errorsAreSuccesses
  \case
    (t, _, m) -> case runKindModule m >>= (`runSynth` t) of 
      Left es -> expectationFailure (unlines $ map show es)
      _       -> return ()
