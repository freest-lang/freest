module KindCheckValidSpec (spec) where

import Syntax.Module qualified as M
import UI.Error (showErrors)
import UnitSpecUtils
import Validation.Kinding (runKindModule, runCheck)

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "Valid kind checking tests" 
  errorsAreFailures
  \src -> \case 
    (t, Nothing, m) -> expectationFailure "Ill formed test case: missing kind annotation"
    (t, Just k , m) -> case runKindModule m >> runCheck m t k of
      Left es -> expectationFailure (showErrors src es)
      _       -> return ()
