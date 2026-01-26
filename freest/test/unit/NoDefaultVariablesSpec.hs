module NoDefaultVariablesSpec (spec) where

import Syntax.Base
import Syntax.Kind qualified as K
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
  \_ (t, _, m) -> noDefault t && noDefault (M.typeDecls m) && noDefault (M.dataDecls m) `shouldBe` True

class NoDefaultVariables a where
  noDefault :: a -> Bool

instance NoDefaultVariables Variable where
  noDefault a = internal a /= defaultInternal

instance NoDefaultVariables (T.Type x) where
  noDefault = \case
    T.Abs _ _ aks t -> all (noDefault . fst) aks && noDefault t
    T.Var _ _ a -> noDefault a
    T.App _ _ t us -> all noDefault (t:us)
    _ -> True

instance NoDefaultVariables (Map.Map a (T.Type x)) where
  noDefault = Map.foldr (\t b -> b && noDefault t) True

instance NoDefaultVariables (Map.Map a ([(Variable, K.Kind)], [Identifier])) where
  noDefault = Map.foldr (\(fst . unzip -> as, _) b -> foldr (\a b' -> noDefault a && b') b as) True

instance NoDefaultVariables (Map.Map a (Identifier, [T.Type x])) where
  noDefault = Map.foldr (\(_, ts) b -> foldr (\t b' -> noDefault t && b') b ts) True
