module RenameYieldsAlphaConguenceSpec (spec) where

import UnitSpecUtils

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Rename

import Data.Map.Strict qualified as Map
import Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "rename t == t"
  errorsAreFailures
  \_ (t, _, m) -> renameYieldsEq (buildDataDecls m) t `shouldBe` True

renameYieldsEq :: TypeDeclMap -> T.Type -> Bool
renameYieldsEq td t = rename td t == t

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
