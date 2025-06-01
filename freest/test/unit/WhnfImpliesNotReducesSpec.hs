module WhnfImpliesNotReducesSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
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
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T is a whnf then T does not reduce" 
  \(t, _, m) -> whnfImpliesNotReduces (buildDataDecls m) t >>= (`shouldBe` True)

whnfImpliesNotReduces :: TypeDeclMap -> T.Type -> IO Bool
whnfImpliesNotReduces m t
  | isWhnf t = catch
    -- Force the deep evaluation of reduce
      (length (show (reduce m t)) `seq` pure False)
      (\(x::ErrorCall) -> pure True)
  | otherwise = pure True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
