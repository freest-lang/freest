module OnlyRenamedVarsAfterRenamingSpec (spec) where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
import Validation.Rename

import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "Only renamed internal numbers for variables in renamed types"
  errorsAreFailures
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of
    Left _ -> expectationFailure "Kinding error"
    Right (m', t') -> onlyRenamed (rename td t') && onlyRenamed td `shouldBe` True
      where td = M.typeDecls m'

class OnlyRenamedVars a where
  onlyRenamed :: a -> Bool

instance OnlyRenamedVars Variable where
  onlyRenamed a = internal a /= defaultInternal

instance OnlyRenamedVars (T.Type x) where
  onlyRenamed = \case
    T.Abs _ _ aks t -> all (onlyRenamed . fst) aks && onlyRenamed t
    T.Var _ _ a -> onlyRenamed a
    T.App _ _ t us -> all onlyRenamed (t : us)
    _ -> True

instance OnlyRenamedVars (Map.Map a (T.Type x)) where
  onlyRenamed = Map.foldr (\t b -> b && onlyRenamed t) True

instance OnlyRenamedVars (Map.Map a ([(Variable, K.Kind)], [Identifier])) where
  onlyRenamed = Map.foldr (\(fst . unzip -> as, _) b -> foldr (\a b' -> onlyRenamed a && b') b as) True

instance OnlyRenamedVars (Map.Map a (Identifier, [T.Type x])) where
  onlyRenamed = Map.foldr (\(_, ts) b -> foldr (\t b' -> onlyRenamed t && b') b ts) True
