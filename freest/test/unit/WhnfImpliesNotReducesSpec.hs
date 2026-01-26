module WhnfImpliesNotReducesSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
import Validation.Normalisation ( isWhnf, reduce )
import UnitSpecUtils

import Control.Exception ( catch, ErrorCall )
import Data.Map.Strict qualified as Map
import Test.Hspec

-- This test should be called with well-formed types only

-- If T reduces then T is not a whnf.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T is a whnf then T does not reduce"
  errorsAreFailures
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of 
    Left es -> expectationFailure "Kinding error"
    Right (m', t') -> whnfImpliesNotReduces >>= (`shouldBe` True)
      where
        whnfImpliesNotReduces
          | isWhnf t' = catch
            -- Force the deep evaluation of reduce
              (length (show (reduce (M.typeDecls m') t')) `seq` pure False)
              (\(x::ErrorCall) -> pure True)
          | otherwise = pure True
