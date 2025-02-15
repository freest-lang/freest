
module EquivalenceInvalidSpec (spec) where

import qualified Syntax.Module                 as M
import           Validation.Base               ( TypeDeclMap )
import           Validation.Kinding            ( runCheck )
import           Validation.TypeEquivalence.TypeEquivalence (equivalent)

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           UnitSpecUtils (mkEquivalenceSpec)

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  ["test/unit/EquivalenceInvalid.test"]
  "Invalid equivalence tests" 
  \(t,u,k,m) -> case runCheck m t k >> runCheck m u k of
    Left es -> expectationFailure (unlines $ map show es)
    _       -> equivalent (buildDataDecls m) t u `shouldBe` False

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
