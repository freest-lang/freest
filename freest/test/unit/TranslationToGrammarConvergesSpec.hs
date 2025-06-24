module TranslationToGrammarConvergesSpec (spec) where

import UnitSpecUtils

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( ValidationState, buildValidationState )
import Validation.TypeEquivalence ( fromType )
import Language.Simple.Grammar

import Data.Map.Strict qualified as Map
import Debug.Trace
import Test.Hspec

-- Requires: This test should be called with well-formed types only

-- Test success is simply termination

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "Type translation to grammar converges" 
  \(t,_,m) -> translateToGrammar (buildValidationState m) t `shouldBe` True

translateToGrammar :: ValidationState -> T.Type -> Bool
translateToGrammar vs t = trace ("\n" ++ show (fromType vs [t])) True

