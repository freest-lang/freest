module RenameYieldsAlphaConguenceSpec (spec) where

import UnitSpecUtils

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
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
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of
    Left _ -> expectationFailure "Kinding error"
    Right (m', t') -> renameYieldsEq `shouldBe` True
      where renameYieldsEq = rename (M.typeDecls m') t' == t'
