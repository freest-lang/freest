module NoDefaultVariablesSpec (spec) where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Unkinded qualified as T

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
  \_ (t, _, m) -> noDefault t && noDefault (snd <$> M.typeDecls m) && noDefault (M.dataTypeDecls m) `shouldBe` True

class NoDefaultVariables a where
  noDefault :: a -> Bool

instance NoDefaultVariables Variable where
  noDefault a = internal a /= defaultInternal

instance NoDefaultVariables a => NoDefaultVariables (Maybe a) where
  noDefault = all noDefault

instance NoDefaultVariables K.Multiplicity where
  noDefault = \case
    K.Sup _ lvφs -> all (noDefault . snd) lvφs
    _            -> True

instance NoDefaultVariables K.Prekind where
  noDefault = \case
    K.VarPK ψ -> noDefault ψ
    _         -> True

instance NoDefaultVariables K.Kind where
  noDefault = \case
    K.Proper _ m pk -> noDefault m && noDefault pk
    K.Arrow _ k1 k2 -> noDefault k1 && noDefault k2
    K.Var _ _ a     -> noDefault a

instance NoDefaultVariables T.ScopedType where
  noDefault = \case
    T.Abs _ aks t -> all noDefaultBnd aks && noDefault t
    T.Var _ a -> noDefault a
    T.App _ t us -> all noDefault (t:us)
    _ -> True

-- | A type-variable binder has no default variables in either its name or its
-- (optional) kind annotation.
noDefaultBnd :: (Variable, Maybe K.Kind) -> Bool
noDefaultBnd (a, mk) = noDefault a && noDefault mk

instance NoDefaultVariables (Map.Map a T.ScopedType) where
  noDefault = Map.foldr (\t b -> b && noDefault t) True

instance NoDefaultVariables (Map.Map a ([(Variable, Maybe K.Kind)], [Identifier])) where
  noDefault = Map.foldr (\(aks, _) b -> all noDefaultBnd aks && b) True

instance NoDefaultVariables (Map.Map a (Identifier, [T.ScopedType])) where
  noDefault = Map.foldr (\(_, ts) b -> foldr (\t b' -> noDefault t && b') b ts) True
