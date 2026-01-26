module KindSynthValidSpec (spec) where

import Validation.Kinding
import UI.Error
import UnitSpecUtils

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "Valid kind synthesis tests" 
  errorsAreSuccesses
  \src -> \case
    (t, _, m) -> case runSynth m t of 
      Left es -> expectationFailure (showErrors src es)
      _       -> return ()
