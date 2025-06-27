module ReductionReflectsSubkindingSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Kind
import Validation.Base ( TypeDeclMap )
import Validation.Normalisation ( isWhnf, reduce )
import Validation.Kinding ( runSynth )
import UI.Error ( Error )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

-- This test should be called with well-formed types only

-- If ⊢ T : κ and T -> U, then ⊢ U : κ.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "If ∆ ⊢ T : κ and T -> U, then ∆ ⊢ U : κ" 
  \(t, _, m) -> reductionPreservesKinding m t `shouldBe` True

reductionPreservesKinding :: M.Module -> T.Type -> Bool
reductionPreservesKinding m t =
  isWhnf t ||
  (trace
    ("\n" ++ show (runSynth m t) ++ " :>? " ++ show (runSynth m (reduce (buildDataDecls m) t))) $
    runSynth m (reduce (buildDataDecls m) t)) <: runSynth m t
  
instance Subsort (Either [Error] Kind) where
  Left _ <: Left _ = True
  Right k <: Right k' = k <: k'
  _ <: _ = False

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
