module WhnfImpliesNotReducesSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Normalisation      ( isWhnf, reduce )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           Control.Exception             ( catch, ErrorCall )

-- This test should be called with well-formed types only

-- If type T reduces then T is not a whnf.

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
      (let !_ = reduce m t in pure False)
      (\(x::ErrorCall) -> pure True)
  | otherwise = pure True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
