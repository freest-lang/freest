module KindCImpliesChanSpec (spec) where

import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import UI.Error (showErrors)
import UnitSpecUtils (mkTypeSpec, errorsAreFailures)
import Validation.Base (emptyValidationState, runValidation)
import Validation.Kinding (chan)

import Control.Monad (when)
import Test.Hspec ( hspec, expectationFailure, shouldBe, Spec )

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "If T of kind C then chan T"
  errorsAreFailures
  \src (t, mk, m) ->
    when (any K.isChannel mk) $
      case runValidation emptyValidationState
             (chan (M.kindSigs m) (M.typeDecls m) t) of
        Left es -> expectationFailure (showErrors src es)
        Right b -> b `shouldBe` True
