module ReduceImpliesNotWhnfSpec (spec) where

import Syntax.Module qualified as M
import Validation.Kinding ( runKindModule )
import Validation.Normalisation ( isWhnf, reduce )
import UI.Error (showErrors)
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Control.Exception ( catch, ErrorCall )
import Debug.Trace ( trace )

-- This test should be called with well-formed types only

-- If T reduces then T is not a whnf

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T reduces then T is not a whnf"
  errorsAreFailures
  \src (t, mk, m) -> 
    case do m' <- runKindModule m 
            t' <- runSynthOrCheck m t mk
            return (m', t')
    of Left es  -> expectationFailure (showErrors src es)
       Right (m', t') -> reducesImpliesNotWhnf >>= (`shouldBe` True)
        where 
          reducesImpliesNotWhnf =
            catch
              (trace ("\n" ++ show t' ++ showWhnf whnf ++ "reduces to " ++ show u')
              pure (not whnf))    -- Force the deep evaluation of reduce
              -- (length (show u) `seq` pure (not whnf)))
              (\(x::ErrorCall) -> pure True)
            where
              u' = reduce m' t'
              whnf = isWhnf t'

showWhnf :: Bool -> String
showWhnf True  = " (a whnf) "
showWhnf False = " (a non whnf) "
