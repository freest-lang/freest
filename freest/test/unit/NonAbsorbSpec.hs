module NonAbsorbSpec (spec) where

import Syntax.Kind qualified as K
import Validation.Rename qualified as R
import Validation.Base ( TypeDeclMap )
import Syntax.Module qualified as M
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec


main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "Non absorbing types"
  \case
    (t, Just k, m) ->
      not (K.isStrictlySession k) ||
      not (R.isAbsorbing (buildDataDecls m) t) ||
      K.isStrictlyAbsorbing k `shouldBe` True
    _ -> expectationFailure "Ill formed test case: missing kind annotation"

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
