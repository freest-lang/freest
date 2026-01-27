module ReductionReflectsSubkindingSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Kind
import Validation.Normalisation ( isWhnf, reduce )
import Validation.Kinding ( runKindModule, runSynth' )
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
  \src (t, _, m) -> case runKindModule m of
    Left es -> expectationFailure (showErrors src es)
    Right m' -> reductionReflectsKinding m' t `shouldBe` True

reductionReflectsKinding :: M.KindedModule -> T.Type -> Bool
reductionReflectsKinding m t =
  isWhnf t ||
  -- (trace
  --   ("\n" ++ show (runSynth' m t) ++ " :>? " ++ show (runSynth' m (reduce (buildTypeDecls m) t))) $
    runSynth' m (reduce m t) <: runSynth' m t
  
instance Subsort (Either [Error] Kind) where
  Left _ <: Left _ = True
  Right k <: Right k' = k <: k'
  _ <: _ = False

