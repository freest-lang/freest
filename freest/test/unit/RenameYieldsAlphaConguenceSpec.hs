module RenameYieldsAlphaConguenceSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename
import qualified Data.Map.Strict               as Map
import           UnitSpecUtils

import           Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/WellFormedTypes.test" 
  "rename t == t" 
  \(t,_,m) -> renameYieldsEq (buildDataDecls m) t `shouldBe` True

renameYieldsEq :: TypeDeclMap -> T.Type -> Bool
renameYieldsEq td t = rename td t == t

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
