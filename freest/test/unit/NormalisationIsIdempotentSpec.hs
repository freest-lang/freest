module NormalisationIsIdempotentSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Normalisation ( normalise )
import UI.Error
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Validation.Kinding ( runKindModule )

-- This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "normalise t == normalise (normalise t)" 
  errorsAreFailures
  \src (t, _, m) -> case runKindModule m of
    Left es  -> expectationFailure (showErrors src es)
    Right m' -> normalisationIsIdempotent m' t `shouldBe` True

normalisationIsIdempotent :: M.KindedModule -> T.Type -> Bool
normalisationIsIdempotent m t = normalise m t == normalise m (normalise m t)
