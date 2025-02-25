module NormalisationIsIdempotentSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Normalisation ( normalise )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Validation.Kinding ( runKindModule )

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "normalise t == normalise (normalise t)" 
  \(t, _, m) -> normalisationIsIdempotent (buildDataDecls m) t `shouldBe` True

normalisationIsIdempotent :: TypeDeclMap -> T.Type -> Bool
normalisationIsIdempotent td t = normalise td t == normalise td (normalise td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
