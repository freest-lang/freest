module RenamePreservesNormalisationSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Rename
import Validation.Normalisation ( normalise, isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T normalises to U, then rename T normalises to rename U" 
  errorsAreFailures
  \_ (t, _, m) -> renamePreservesNormalisation (buildDataDecls m) t `shouldBe` True

renamePreservesNormalisation :: TypeDeclMap -> T.Type -> Bool
renamePreservesNormalisation td t = isWhnf t || u == u'
  where u  = normalise td t
        u' = normalise td (rename td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
