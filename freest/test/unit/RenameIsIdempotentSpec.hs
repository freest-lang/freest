module RenameIsIdempotentSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "rename(t) == rename(rename(t))" 
  \(t,_,m) -> renameIsIdempotent (buildDataDecls m) t `shouldBe` True

renameIsIdempotent :: TypeDeclMap -> T.Type -> Bool
renameIsIdempotent td t = rename td t == rename td (rename td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
