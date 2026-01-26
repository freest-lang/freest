module WhnfOrReducesSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runCheck, runKindModule )
import Validation.Normalisation ( isWhnf, reduce )

import Control.Monad (void)
import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

-- A given type T is either a WHNF or reduces

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "A given type T is either a whnf or reduces"
  errorsAreFailures
  \src (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of 
    Left es -> expectationFailure "Kinding error"
    Right (m', t') -> whnfOrReduces `shouldBe` True
      where whnfOrReduces = isWhnf t' || let !_ = reduce (M.typeDecls m') t' in True
