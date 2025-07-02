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

-- If ⊢ T : κ and T -> U, then ⊢ U :  κ' and k' <: k

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If ∆ ⊢ T : κ and T -> U, then ∆ ⊢ U : κ' and k' <: k"
  errorsAreFailures
  \(t, _, m) -> reductionReflectsKinding m t `shouldBe` True

reductionReflectsKinding :: M.Module -> T.Type -> Bool
reductionReflectsKinding m t =
  isWhnf t ||
  (trace
    ("\n" ++ show (runSynth m t) ++ " :>? " ++ show (runSynth m (reduce (buildTypeDecls m) t))) $
    runSynth m (reduce (buildTypeDecls m) t)) <: runSynth m t
  
instance Subsort (Either [Error] Kind) where
  Left _ <: Left _ = True
  Right k <: Right k' = k <: k'
  _ <: _ = False

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
