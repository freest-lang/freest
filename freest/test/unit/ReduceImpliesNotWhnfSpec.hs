module ReduceImpliesNotWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
import Validation.Normalisation ( isWhnf, reduce )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Control.Exception ( catch, ErrorCall )

-- This test should be called with well-formed types only

-- If T reduces then T is not a whnf.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T reduces then T is not a whnf"
  errorsAreFailures
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of
    Left _ -> expectationFailure "Kinding error"
    Right (m', t') -> reducesImpliesNotWhnf >>= (`shouldBe` True)
      where
        reducesImpliesNotWhnf = catch
          -- Force the deep evaluation of reduce
          (length (show (reduce (M.typeDecls m') t')) `seq` pure (not (isWhnf t')))
          (\(x::ErrorCall) -> pure True)

