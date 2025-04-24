module KindCheckValidSpec (spec) where

import           Validation.Kinding
import           UnitSpecUtils
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"]
  "Valid kind checking tests" 
  \case
    (t, Nothing, m) -> expectationFailure "Ill formed test case: missing kind annotation"
    (t, Just k, m) -> case runKindModule m >>= \m -> runCheck m t k of 
      Left es -> expectationFailure (unlines $ map show es)
      _       -> return ()
