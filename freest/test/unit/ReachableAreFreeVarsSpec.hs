module ReachableAreFreeVarsSpec (spec) where

import Syntax.Module qualified as M
import Validation.Base ( TypeDeclMap )
import Validation.Substitution ( freeVars )
import Validation.Rename ( reachable )

import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

-- reach(T) ⊆ fv(T)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "Free reachable variables are free" 
  \(t, _, m) -> freeVars t `Set.isSubsetOf` reachable (buildTypeDecls m) t `shouldBe` True

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
