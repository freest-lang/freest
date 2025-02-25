module KindInvalidSpec (spec) where

import Validation.Kinding ( runSynth, runCheck, runKindModule )

import Data.Either ( isRight )
import Data.Map qualified as Map
import Test.Hspec
import UnitSpecUtils ( mkKindingSpec )

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/IllFormedTypes.test"]
  "Invalid kinding tests" 
  \case
    (t, Just k, m) -> case runKindModule m >>= \m -> runCheck m t k of
      Left _ -> return ()
      Right _ -> expectationFailure "An error was expected but none was thrown."
    (t, Nothing, m) -> case runKindModule m >>= (`runSynth` t) of 
      Left _ -> return ()
      Right _ -> expectationFailure "An error was expected but none was thrown."
