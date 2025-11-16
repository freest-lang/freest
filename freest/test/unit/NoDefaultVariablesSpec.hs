module NoDefaultVariablesSpec (spec) where

import Syntax.Base
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap, DataDeclMap )

import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "Only proper internal numbers for variables" 
  errorsAreFailures
  \_ (t, _, m) -> noDefault t && noDefault (buildTypeDecls m) && noDefault (buildDataDecls m) `shouldBe` True

class NoDefaultVariables a where
  noDefault :: a -> Bool

instance NoDefaultVariables Variable where
  noDefault a = internal a /= defaultInternal

instance NoDefaultVariables T.Type where
  noDefault = \case
    T.Abs _ aks t -> all (noDefault . fst) aks && noDefault t
    T.Var _ a -> noDefault a
    T.App _ t us -> all noDefault (t:us)
    _ -> True

instance NoDefaultVariables TypeDeclMap where
  noDefault = Map.foldr (\t b -> b && noDefault t) True

instance NoDefaultVariables DataDeclMap where
  noDefault m = True -- TODO: complete me!

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
buildDataDecls :: M.Module -> DataDeclMap
buildDataDecls m = Map.fromList (map (\(i, aks, cds) -> (i, (aks, Map.fromList cds))) $ M.dataDecls m)
