module RenamePreservesReductionSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Rename
import Validation.Normalisation ( reduce, isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T reduces to U, then rename T reduces to rename U"
  errorsAreFailures
  \_ (t, _, m) -> renamePreservesReduction (buildDataDecls m) t `shouldBe` True

renamePreservesReduction :: TypeDeclMap -> T.Type -> Bool
renamePreservesReduction td t = isWhnf t || u == u'
  where u  = reduce td t
        u' = reduce td (rename td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
