module AbsorbingSpec (spec) where

import Syntax.Base ( getSpan )
import Syntax.Kind
import Validation.Rename qualified as R
import Validation.Base ( TypeDeclMap )
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
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test" ]
  "Absorbing types have kind <: 1S"
  \case
    (t, Just k, m) -> not (R.absorbing (buildDataDecls m) t) || k <: ls (getSpan k) `shouldBe` True
    -- (t, Just k, m) -> not (K.isStrictlyAbsorbing k) || R.absorbing (buildDataDecls m) t `shouldBe` True
    _ -> expectationFailure "Ill formed test case: missing kind annotation"

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
