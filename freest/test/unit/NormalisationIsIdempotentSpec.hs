module NormalisationIsIdempotentSpec (spec) where

import Syntax.Module qualified as M
import Validation.Normalisation ( normalise )
import UI.Error
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Validation.Kinding ( runKindModule, runCheck )

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "normalise t == normalise (normalise t)" 
  errorsAreFailures
  \src (t, mk, m) -> 
    case do m' <- runKindModule m 
            t' <- runSynthOrCheck m t mk
            return (m', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (m', t') -> normalisationIsIdempotent `shouldBe` True
        where normalisationIsIdempotent = 
                normalise m' t' == normalise m' (normalise m' t')
