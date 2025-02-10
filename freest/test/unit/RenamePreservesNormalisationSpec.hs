module RenamePreservesNormalisationSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename
import           Validation.Normalisation      ( normalise, isWhnf )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/KindingValid.test"] 
  "If T normalises to U, then rename T normalises to rename U" 
  \(t,_,m) -> renamePreservesNormalisation (buildDataDecls m) t `shouldBe` True

renamePreservesNormalisation :: TypeDeclMap -> T.Type -> Bool
renamePreservesNormalisation td t = isWhnf t || u == u'
  where u  = normalise td t
        u' = normalise td (rename td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
