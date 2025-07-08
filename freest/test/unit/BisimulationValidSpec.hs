module BisimulationValidSpec (spec) where

import Syntax.Module qualified as M
import Validation.Base ( buildValidationState )
import Validation.Kinding ( runCheck )
import Validation.TypeEquivalence ( fromType )
import UnitSpecUtils ( mkEquivalenceSpec )
import Language.Simple.Bisimulation ( bisimilar )

import Data.Map.Strict qualified as Map
import Debug.Trace ( trace )
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkEquivalenceSpec
  ["test/unit/EquivalenceValid.test"]
  "Valid type equivalence tests" 
  \(t, u, k, m) -> case runCheck m t k >> runCheck m u k of
    Left es -> expectationFailure (unlines $ map show es)
    _       ->
      trace ("\n" ++ show t ++ " vs. " ++ show u)
      bisimilar (fromType (buildValidationState m) [t, u])  `shouldBe` True
