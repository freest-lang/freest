module NormalisationYieldsWhnfSpec (spec) where

import Syntax.Module qualified as M
import Validation.Kinding (runKindModule)
import Validation.Normalisation ( normalise, isWhnf )
import UI.Error (showErrors)
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
-- import           Debug.Trace

-- This test should be called with well-formed types only

-- Note: this spec tests very little. As it is, the normalise function returns a
-- whnf, if it returns at all.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T normalises to U, then U is a whnf" 
  errorsAreFailures
  \src (t, mk, m) -> 
    case do m' <- runKindModule m 
            t' <- runSynthOrCheck m t mk
            return (m', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (m', t') -> normYieldsWhnf `shouldBe` True
        where normYieldsWhnf = isWhnf (normalise m' t')
