module NotWhnfImpliesReducesSpec (spec) where

import Syntax.Module qualified as M
import UI.Error (showErrors)
import Validation.Kinding ( runKindModule )
import Validation.Normalisation ( isWhnf, reduce )

import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

-- If is not a whnf then T reduces.


main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "A given type T is either a whnf or reduces"
  errorsAreFailures
  \src (t, mk, m) -> 
    case do m' <- runKindModule m 
            t' <- runSynthOrCheck m t mk
            return (m', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (m', t') -> whnfOrReduces `shouldBe` True
        where whnfOrReduces = isWhnf t' || let !_ = reduce m' t' in True

