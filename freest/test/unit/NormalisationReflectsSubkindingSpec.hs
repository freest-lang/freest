module NormalisationReflectsSubkindingSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Kind
import Validation.Base ( TypeDeclMap )
import Validation.Normalisation ( normalise )
import Validation.Kinding ( runSynth )
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
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "If ∆ ⊢ T : κ and T normalises to U, then ∆ ⊢ U : κ' and k' <: k"
  \(t, _, m) -> normalisationReflectsKinding m t `shouldBe` True

normalisationReflectsKinding :: M.Module -> T.Type -> Bool
normalisationReflectsKinding m t =
  trace ("\n" ++ show t ++ " : " ++ show k1 ++ " :>? " ++ show u ++ " : " ++ show k2) $
  k2 <: k1
  where k1 = runSynth m t
        u  = normalise (buildDataDecls m) t
        k2 = runSynth m u
  
instance Subsort (Either [Error] Kind) where
  Left _ <: Left _ = True
  Right k <: Right k' = k <: k'
  _ <: _ = False

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
