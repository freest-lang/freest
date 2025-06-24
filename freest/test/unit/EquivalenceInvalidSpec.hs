
module EquivalenceInvalidSpec (spec) where

import Syntax.Module qualified as M
import Validation.Base ( buildValidationState )
import Validation.Kinding ( runCheck )
import Validation.TypeEquivalence ( equivalent )

import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils ( mkEquivalenceSpec )

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  ["test/unit/EquivalenceInvalid.test"]
  "Invalid equivalence tests" 
  \(t,u,k,m) -> case runCheck m t k >> runCheck m u k of
    Left es -> expectationFailure (unlines $ map show es)
    _       -> equivalent (buildValidationState m) t u `shouldBe` False
