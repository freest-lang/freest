module ReductionReflectsSubkindingSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Kind
import Validation.Normalisation ( isWhnf, reduce )
import Validation.Kinding ( runKindModule, runSynth )
import UI.Error ( Error, showErrors )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

-- This test should be called with well-formed types only

-- If ⊢ T : κ and T -> U, then ⊢ U :  κ' and k' <: k

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If ∆ ⊢ T : κ and T -> U, then ∆ ⊢ U : κ' and k' <: k"
  errorsAreFailures
  \src (t, mk, m) -> 
    case do m' <- runKindModule m 
            t' <- runSynthOrCheck m t mk
            return (m', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (m', t') -> reductionReflectsKinding `shouldBe` True
        where
          reductionReflectsKinding = 
            isWhnf t' || TK.kindOf (reduce m' t') <: TK.kindOf t'

