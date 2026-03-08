module KindSynthValidSpec (spec) where

import Syntax.Module qualified as M
import UI.Error (showErrors)
import UnitSpecUtils
import Validation.Kinding (runKindModule, runSynth)
import Validation.PolyRecursion (runCheckPolyRec)

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "Valid kind synthesis tests" 
  errorsAreSuccesses
  \src -> \case
    (t, _, m) -> case runKindModule m >>= runCheckPolyRec >> runSynth m t of 
      Left es -> expectationFailure (showErrors src es)
      _       -> return ()
