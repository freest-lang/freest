module ReductionPreservesReflectsAbsorbingSpec (spec) where

import Syntax.Base ( getSpan )
import Syntax.Kind
import Syntax.Module qualified as M
import Validation.Base ( TypeDeclMap )
import Validation.Rename
import Validation.Normalisation
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test" ]
  "Normalisation preserves and reflect absorbing"
  \case
    (t, Just k, m) ->
      isWhnf t || 
      (let td = buildTypeDecls m in
        trace (show t ++ " vs. " ++ show (reduce td t)) $
        absorbing td t == absorbing td (reduce td t)) `shouldBe` True
    _ -> expectationFailure "Ill formed test case: missing kind annotation"

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
