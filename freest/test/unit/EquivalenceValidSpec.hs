module EquivalenceValidSpec (spec) where

import qualified Syntax.Module                 as M
import           Validation.Base               ( TypeDeclMap )
import           Validation.TypeEquivalence.TypeEquivalence (equivalent)
import           UnitSpecUtils                 (mkEquivalenceSpec)

import qualified Data.Map.Strict               as Map
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  ["test/unit/EquivalenceValid.test"]
  "Valid type equivalence tests" 
  \(t,u,m) -> equivalent (buildDataDecls m) t u `shouldBe` True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
