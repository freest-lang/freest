module RenamePreservesWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Rename
import Validation.Normalisation ( isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "T is a whnf iff rename T is a whnf"
  errorsAreFailures
  \(t, _, m) -> renamePreservesWhnf (buildDataDecls m) t `shouldBe` True

renamePreservesWhnf :: TypeDeclMap -> T.Type -> Bool
renamePreservesWhnf td t = isWhnf t == isWhnf (rename td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
