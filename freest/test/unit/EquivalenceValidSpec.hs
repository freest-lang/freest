module EquivalenceValidSpec (spec) where

import Syntax.Module qualified as M
import Validation.Base ( TypeDeclMap )
import Validation.TypeEquivalence ( equivalent )
import UI.Error ( showErrors )
import UnitSpecUtils ( mkEquivalenceSpec )

import Data.Map.Strict qualified as Map
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  ["test/unit/EquivalenceValid.test"]
  "Valid type equivalence tests" 
  \src (t,u,k,m) -> equivalent (M.typeDecls m) t u `shouldBe` True
