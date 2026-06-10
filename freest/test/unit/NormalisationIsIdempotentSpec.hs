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
  \src (t, mk, modl) -> 
    case do (kctx, modl') <- runKindModule modl
            t' <- runSynthOrCheck kctx t mk
            return (modl', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (modl', t') -> 
        if nt' == nnt' then return () 
        else expectationFailure (show nt' ++ "\n/=\n" ++ show nnt')-- `shouldBe` True
        where
          nt'  = normalise modl' t' 
          nnt' = normalise modl' nt'
