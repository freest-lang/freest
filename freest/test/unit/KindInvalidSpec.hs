module KindInvalidSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Validation.Kinding ( runSynth, runCheck, runKindModule )
import Validation.PolyRecursion ( runCheckPolyRec )

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
    (t, k, m) -> case do runKindModule m >>= runCheckPolyRec >> runSynthOrCheck m t k of
      Left _ -> return ()
      Right _ -> expectationFailure "An error was expected but none was thrown"

    -- (t, mk, m) -> case runKindModule m >> runSynthOrCheck m t mk of
    --   Left _ -> return ()
    --   Right t' -> expectationFailure $ "An error was expected but none was thrown.\n" ++ show t'

