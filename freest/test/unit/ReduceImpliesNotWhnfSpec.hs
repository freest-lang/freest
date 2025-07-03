module ReduceImpliesNotWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Normalisation ( isWhnf, reduce )
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
  \(t, _, m) -> reducesImpliesNotWhnf (buildTypeDecls m) t >>= (`shouldBe` True)

reducesImpliesNotWhnf :: TypeDeclMap -> T.Type -> IO Bool
reducesImpliesNotWhnf m t =
  catch
    (trace ("\n" ++ show t ++ showWhnf whnf ++ "reduces to " ++ show u)
     pure (not whnf))    -- Force the deep evaluation of reduce
    -- (length (show u) `seq` pure (not whnf)))
    (\(x::ErrorCall) -> pure True)
  where
    u = reduce m t
    whnf = isWhnf t

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls

showWhnf :: Bool -> String
showWhnf True  = " (a whnf) "
showWhnf False = " (a non whnf) "
