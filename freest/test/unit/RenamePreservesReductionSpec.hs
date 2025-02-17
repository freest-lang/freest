module RenamePreservesReductionSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename
import           Validation.Normalisation      ( reduce, isWhnf )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/WellFormedTypes.test" 
  "If T reduces to U, then rename T reduces to rename U" 
  \(t,_,m) -> renamePreservesReduction (buildDataDecls m) t `shouldBe` True

renamePreservesReduction :: TypeDeclMap -> T.Type -> Bool
renamePreservesReduction td t = isWhnf t || u == u'
  where u  = reduce td t
        u' = reduce td (rename td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
