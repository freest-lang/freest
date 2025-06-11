module ReduceImpliesNotWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
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
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T reduces then T is not a whnf" 
  \(t, _, m) -> reducesImpliesNotWhnf (buildDataDecls m) t >>= (`shouldBe` True)

reducesImpliesNotWhnf :: TypeDeclMap -> T.Type -> IO Bool
reducesImpliesNotWhnf m t =
  catch
    -- Force the deep evaluation of reduce
    (length (show (reduce m t)) `seq` pure (not (isWhnf t)))
    (\(x::ErrorCall) -> pure True)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
