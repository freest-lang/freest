module ChanIffChannelKindSpec (spec) where

import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import UI.Error (showErrors)
import UnitSpecUtils (mkTypeSpec, errorsAreFailures)
import Validation.Kinding (chan, runKindModule, runSynth)

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "chan T ⟺ kindOf T == 1C"
  errorsAreFailures
  \src (t, _, m) ->
    case runKindModule m >>= \(kctx, _) -> runSynth kctx t of
      Left es  -> expectationFailure (showErrors src es)
      Right kt -> chan (M.kindSigs m) (M.typeDecls m) t `shouldBe` is1C (TK.kindOf kt)
  where
    is1C :: K.Kind -> Bool
    is1C (K.Proper _ K.Lin{} K.Channel) = True
    is1C _                              = False
