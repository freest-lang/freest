module BisimulationValidSpec (spec) where

import Syntax.Module qualified as M
import UI.Error ( showErrors )
import Validation.Kinding ( runCheck' )
import Validation.TypeEquivalence ( fromTypes, showGrammar )
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
  \src (t, u, k, m) -> case runCheck' (M.asScoped m) t k 
                         >> runCheck' (M.asScoped m) u k of
    Left es -> expectationFailure (showErrors src es)
    _       ->
      bisimilar ps xs ys `shouldBe` True
      where g@(ps, [xs, ys]) = fromTypes m [t, u]
