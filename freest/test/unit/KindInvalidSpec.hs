module KindInvalidSpec (spec) where

import Syntax.Module qualified as M
import Validation.Kinding ( runSynth, runCheck, runKindModule )

import Data.Either ( isRight )
import Data.Map qualified as Map
import Test.Hspec
import UnitSpecUtils ( mkTypeSpec, errorsAreSuccesses, runSynthOrCheck )

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/IllFormedTypes.test"]
  "Invalid kinding tests" 
  errorsAreSuccesses
  \_ -> \case
    (t, mk, m) -> case runKindModule m >> runSynthOrCheck m t mk of
      Left _ -> return ()
      Right t' -> expectationFailure $ "An error was expected but none was thrown.\n" ++ show t'
