module NormalisationReflectsSubkindingSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Kind
import Validation.Base ( ValidationState, buildValidationState )
import Validation.Normalisation ( normalise )
import Validation.Kinding ( runSynth' )
import UnitSpecUtils
import UI.Error ( Error )

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

-- This test should be called with well-formed types only

-- If ⊢ T : κ and T normalises to U, then ⊢ U : κ.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If ∆ ⊢ T : κ and T normalises to U, then ∆ ⊢ U : κ' and k' <: k"
  errorsAreFailures
  \(t, _, m) -> normalisationReflectsKinding (buildValidationState m) t `shouldBe` True

normalisationReflectsKinding :: ValidationState -> T.Type -> Bool
normalisationReflectsKinding vs t =
  trace ("\n" ++ show t ++ " : " ++ show k1 ++ " :>? " ++ show u ++ " : " ++ show k2) $
  k2 <: k1
  where k1 = runSynth' vs Map.empty t
        u  = normalise vs t
        k2 = runSynth' vs Map.empty u
  
instance Subsort (Either [Error] Kind) where
  Left _ <: Left _ = True
  Right k <: Right k' = k <: k'
  _ <: _ = False
