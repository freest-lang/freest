module AbsorbingTypesAreSessionTypesSpec (spec) where

import Syntax.Base ( getSpan )
import Syntax.Kind
import Validation.Rename qualified as R
import Validation.Base ( buildValidationState )
import Syntax.Module qualified as M
import UnitSpecUtils
import Validation.Kinding ( runSynth )

import Data.Either
import Test.Hspec
import Debug.Trace ( trace )

main :: IO ()
main = hspec spec

{-
The inverse of this test is not (no longer) valid. There are absorbing types
that are not channel types. Non-contractive types are one (the?) example.
-}
spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "Absorbing types have kind <: 1S"
  errorsAreFailures
  \cases
    _ (t, _, m) -> 
      trace ("\n" ++ show t ++ " : " ++ show k ++ showAbs absorbing) $
      not absorbing || isSession k `shouldBe` True
      where
        absorbing = R.absorbing (buildValidationState m) t
        k = fromRight (error "should not happen") $ runSynth m t

showAbs :: Bool -> String
showAbs True = " is absorbing"
showAbs False = " is not absorbing"
