module TranslationToGrammarConvergesSpec (spec) where

import UnitSpecUtils

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
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
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "Type translation to grammar converges"
  errorsAreFailures
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of
    Left _ -> expectationFailure "Kinding error"
    Right (m', t') -> translateToGrammar `shouldBe` True
      where
        translateToGrammar = trace ("\n" ++ show (fromType (M.typeDecls m') [t'])) True

