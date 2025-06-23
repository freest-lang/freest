module OnlyRenamedVarsAfterRenamingSpec (spec) where

import Syntax.Base
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Rename

import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "Only renamed internal numbers for variables in renamed types" 
  \(t, _, m) ->
    let td = buildTypeDecls m
    in onlyRenamed (rename td t) && onlyRenamed td `shouldBe` True

class OnlyRenamedVars a where
  onlyRenamed :: a -> Bool

instance OnlyRenamedVars Variable where
  onlyRenamed a = internal a /= defaultInternal

instance OnlyRenamedVars T.Type where
  onlyRenamed = \case
    T.Abs _ aks t -> all (onlyRenamed . fst) aks && onlyRenamed t
    T.Var _ a -> onlyRenamed a
    T.App _ t us -> all onlyRenamed (t:us)
    _ -> True

instance OnlyRenamedVars TypeDeclMap where
  onlyRenamed = Map.foldr (\t b -> b && onlyRenamed t) True

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
