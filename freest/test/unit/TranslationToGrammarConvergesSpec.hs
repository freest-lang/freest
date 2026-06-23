module TranslationToGrammarConvergesSpec (spec) where

import UnitSpecUtils

import Syntax.Module qualified as M
import UI.Error (showErrors)
import Validation.Kinding (runKindModule)
import Validation.TypeEquivalence ( fromTypes, showGrammar )

import Language.Simple.Grammar

import Test.Hspec
import Debug.Trace ( trace )

-- Requires: This test should be called with well-formed types only

-- Test success is simply termination

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "Type translation to grammar converges"
  errorsAreFailures
  \src (t, mk, modl) -> 
    case do (kctx, modl') <- runKindModule modl 
            t' <- runSynthOrCheck kctx t mk
            return (modl', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (modl', t') -> translateToGrammar `shouldBe` True
        where translateToGrammar = length (showGrammar g) > 1
              g@(productions, _) = fromTypes (M.typeDecls modl') [t']
