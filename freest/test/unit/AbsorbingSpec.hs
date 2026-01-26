module AbsorbingSpec (spec) where

import Validation.Kinding ( runKindModule, runCheck )
import Validation.Rename ( isAbsorbing )
import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec

main :: IO ()
main = hspec spec

{-
The inverse of this test is not (no longer) valid. There are absorbing types
that are not channel types. Non-contractive types are one (the?) example.
-}
spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test" ]
  "Channel types (kind C) are absorbing types"
  errorsAreFailures
  \_ -> \case
    (t, Just k, m) -> case (,) <$> runKindModule m <*> runCheck m t k of 
      Left es -> expectationFailure "Kinding error"
      Right (m', t') -> not (k K.<: K.lc nullSpan) || isAbsorbing (M.typeDecls m') t' `shouldBe` True
    _ -> expectationFailure "Ill formed test case: missing kind annotation"