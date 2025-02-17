module OnlyRenamedVarsAfterRenamingSpec (spec) where

import           Syntax.Base
import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           UnitSpecUtils

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/WellFormedTypes.test" 
  "Only renamed internal numbers for variables in renamed types" 
  \(t, _, m) ->
    let td = buildTypeDecls m
        (t', td') = (rename td t, td) -- TODO: fix me!
    in onlyRenamed t' && onlyRenamed td' `shouldBe` True

class OnlyRenamedVars a where
  onlyRenamed :: a-> Bool

instance OnlyRenamedVars Variable where
  onlyRenamed a = internal a <= firstRenamed

instance OnlyRenamedVars T.Type where
  onlyRenamed = \case
    T.Quant _ _ a _ t -> onlyRenamed a && onlyRenamed t
    T.Var _ a -> onlyRenamed a
    T.App _ t us -> all onlyRenamed (t:us)
    _ -> True

instance OnlyRenamedVars TypeDeclMap where
  onlyRenamed = Map.foldr (\(as, t) b -> b && all onlyRenamed as && onlyRenamed t) True

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
