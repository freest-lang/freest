module TranslationToGrammarConvergesSpec (spec) where

import UnitSpecUtils

import Syntax.Module qualified as M
import Syntax.Type qualified as T
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
  \src (t, _, m) -> case runKindModule m of 
    Left es  -> expectationFailure (showErrors src es) 
    Right m' -> translateToGrammar m' t `shouldBe` True

translateToGrammar :: M.KindedModule -> T.Type -> Bool
translateToGrammar m t =
  -- trace (" " ++ show (length productions) ++ " productions") True
  trace ("\n" ++ showGrammar g) True
  where g@(productions, _) = fromTypes m [t]
